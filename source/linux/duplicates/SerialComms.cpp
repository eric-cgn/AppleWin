/*
AppleWin : An Apple //e emulator for Windows

Copyright (C) 1994-1996, Michael O'Brien
Copyright (C) 1999-2001, Oliver Schmidt
Copyright (C) 2002-2005, Tom Charlesworth
Copyright (C) 2006-2009, Tom Charlesworth, Michael Pohoreski, Nick Westgate

AppleWin is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

AppleWin is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with AppleWin; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

/* Description: Super Serial Card emulation
 *
 * Author: Various
 */

// Refs:
// [Ref.1] AppleWin\docs\SSC Memory Locations for Programmers.txt
// [Ref.2] SSC recv IRQ example: https://sites.google.com/site/drjohnbmatthews/apple2/ssc - John B. Matthews, 5/13/87
// [Ref.3] SY6551 info: http://users.axess.com/twilight/sock/rs232pak.html
//
// SSC-pg is an abbreviation for pages references to "Super Serial Card, Installation and Operating Manual" by Apple

#include "StdAfx.h"

#include "SerialComms.h"
#include "CPU.h"
#include "Interface.h"
#include "Log.h"
#include "Memory.h"
#include "Registry.h"
#include "YamlHelper.h"
#include <sys/socket.h>
#include <sys/ioctl.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <unistd.h>
#include <termios.h>
#include "../resource/resource.h"

#include <thread>
#include <mutex>

#define MS_RLSD_ON 0x1
#define MS_DSR_ON 0x2
#define MS_CTS_ON 0x4

#define TCP_SERIAL_PORT 1977

#define CRIT_RECV 0 //guard critical sections around recv buffer
#define CRIT_RTS 1 //used as a sync primitive to block recv thread on rts low
#define CRIT_MAX 2



// Default: 9600-8-N-1
SSC_DIPSW CSuperSerialCard::m_DIPSWDefault =
{
    // DIPSW1:
    B9600, //baud        // Use 9600, as a 1MHz Apple II can only handle up to 9600 bps [Ref.1]
    FWMODE_CIC,

    // DIPSW2:
    1, //stop bits
    8,                // ByteSize
    0, //parity
    false,            // SW2-5: LF(0x0A). SSC-24: In Comms mode, SSC automatically discards LF immediately following CR
    true,            // SW2-6: Interrupts. SSC-47: Passes interrupt requests from ACIA to the Apple II. NB. Can't be read from software
};

//===========================================================================

CSuperSerialCard::CSuperSerialCard(UINT slot) :
    Card(CT_SSC, slot),
    m_strSerialPortChoices(1, '\0'), // Combo box friendly, just in case.
    m_uTCPChoiceItemIdx(0),
    m_bCfgSupportDCD(false),
    m_pExpansionRom(NULL)
{
    if (m_slot != 2)    // fixme
        ThrowErrorInvalidSlot();
    
    m_CriticalSection = new std::mutex[CRIT_MAX]();

    m_dwSerialPortItem = 0;

    m_hCommHandle = INVALID_HANDLE_VALUE;
    m_hCommListenSocket = INVALID_SOCKET;
    m_hCommAcceptSocket = INVALID_SOCKET;

    m_hCommThread = NULL;

    for (UINT i=0; i<COMMEVT_MAX; i++)
        m_hCommEvent[i] = NULL;

    memset(&m_o, 0, sizeof(m_o));

    InternalReset();

    //

    const size_t SERIALCHOICE_ITEM_LENGTH = 12;
    char serialPortName[SERIALCHOICE_ITEM_LENGTH];
    std::string regSection = RegGetConfigSlotSection(m_slot);
    RegLoadString(regSection.c_str(), REGVALUE_SERIAL_PORT_NAME, TRUE, serialPortName, sizeof(serialPortName), TEXT(""));

    SetSerialPortName(serialPortName);
}

void CSuperSerialCard::InternalReset()
{
    const std::lock_guard<std::mutex> lock(((std::mutex*)m_CriticalSection)[CRIT_RECV]); // for clearing tcp buffer
    GetDIPSW();

    // SY6551 datasheet: Hardware reset sets Command register to 0
    // . NB. MOS6551 datasheet: Hardware reset: b#00000010 (so ACIA not init'd on IN#2!)
    // SY6551 datasheet: Hardware reset sets Control register to 0 - the DIPSW settings are not used by h/w to setup this register
    UpdateCommandAndControlRegs(0, 0);    // Baud=External clock! 8-N-1

    //

    m_vbTxIrqPending = false;
    m_vbRxIrqPending = false;
    m_vbTxEmpty = true;

    m_vuRxCurrBuffer = 0;
    m_qComSerialBuffer[0].clear();
    m_qComSerialBuffer[1].clear();
    m_qTcpSerialBuffer.clear();

    m_uDTR = 0; //enable
    m_uRTS = 0; //enable
    m_dwModemStatus = m_kDefaultModemStatus;
}

CSuperSerialCard::~CSuperSerialCard()
{
    CloseComm();
    if(m_CriticalSection){
        delete [] (std::mutex*)m_CriticalSection;
    }
    delete [] m_pExpansionRom;
    m_pExpansionRom = NULL;
}

//===========================================================================

// TODO: Serial Comms - UI Property Sheet Page:
// . Ability to config the 2x DIPSWs - only takes affect after next Apple2 reset
// . 'Default' button that resets DIPSWs to DIPSWDefaults
// . Must respect IRQ disable dipswitch (cannot be overridden or read by software)

void CSuperSerialCard::GetDIPSW()
{
    // TODO: Read settings from Registry(?). In the meantime, use the defaults:
    SetDIPSWDefaults();
}

void CSuperSerialCard::SetDIPSWDefaults()
{
    // Default DIPSW settings (comms mode)

    // DIPSW1:
    m_DIPSWCurrent.uBaudRate        = m_DIPSWDefault.uBaudRate;
    m_DIPSWCurrent.eFirmwareMode    = m_DIPSWDefault.eFirmwareMode;

    // DIPSW2:
    m_DIPSWCurrent.uStopBits        = m_DIPSWDefault.uStopBits;
    m_DIPSWCurrent.uByteSize        = m_DIPSWDefault.uByteSize;
    m_DIPSWCurrent.uParity            = m_DIPSWDefault.uParity;
    m_DIPSWCurrent.bLinefeed        = m_DIPSWDefault.bLinefeed;
    m_DIPSWCurrent.bInterrupts        = m_DIPSWDefault.bInterrupts;
}

UINT CSuperSerialCard::BaudRateToIndex(UINT uBaudRate)
{
    switch (uBaudRate)
    {
    case 110: return 0x05;
    case 300: return 0x06;
    case 600: return 0x07;
    case 1200: return 0x08;
    case 2400: return 0x0A;
    case 4800: return 0x0C;
    case 9600: return 0x0E;
    case 19200: return 0x0F;
    case 115200: return 0x00;
    }

    _ASSERT(0);
    LogFileOutput("SSC: BaudRateToIndex(): unsupported rate: %d\n", uBaudRate);
    return BaudRateToIndex(m_kDefaultBaudRate);    // nominally use AppleWin default
}

//===========================================================================

void CSuperSerialCard::UpdateCommState()
{
    //N/A for TCP
}

//===========================================================================

bool CSuperSerialCard::CheckComm()
{
    const int enable = 1;
    // check for COM or TCP socket handle, and setup if invalid
    if (IsActive())
        return true;

    if (m_dwSerialPortItem == m_uTCPChoiceItemIdx)
    {
        m_hCommListenSocket = socket(AF_INET, SOCK_STREAM, 0);
        if (m_hCommListenSocket == INVALID_SOCKET)
        {
            return false;
        }
        // have socket so attempt to bind it
        struct sockaddr_in saAddress;
        memset(&saAddress, 0, sizeof(sockaddr_in));
        saAddress.sin_family = AF_INET;
        saAddress.sin_port = htons(TCP_SERIAL_PORT); // TODO: get from registry / GUI
        saAddress.sin_addr.s_addr = htonl(INADDR_ANY);
        if (setsockopt(m_hCommListenSocket, SOL_SOCKET, SO_REUSEADDR, &enable, sizeof(int)) < 0){
            _ASSERT(0);
            LogFileOutput("SSC: CommCommand(): unsupported Echo mode. Command=0x%02X\n", m_uCommandByte);
        }
        if (bind(m_hCommListenSocket, (struct sockaddr *)&saAddress, sizeof(saAddress)) == -1)
        {
            m_hCommListenSocket = INVALID_SOCKET;
            return false;
        }
        if (listen(m_hCommListenSocket, 1) == -1)
        {
            m_hCommListenSocket = INVALID_SOCKET;
            return false;
        }
        //make thread for accept connect read close
        CommThInit();
    }
    else if (m_dwSerialPortItem)
    {
        return false;
    }
    return IsActive();
}

//===========================================================================

void CSuperSerialCard::CloseComm()
{
    CommTcpSerialCleanup();
    CommThUninit();
}

void CSuperSerialCard::CommTcpSerialCleanup()
{
    CommTcpSerialClose();
}

void CSuperSerialCard::CommTcpSerialClose()
{
    const std::lock_guard<std::mutex> lock(((std::mutex*)m_CriticalSection)[CRIT_RECV]); // for clearing tcp buffer
    //close all sockets
    m_qTcpSerialBuffer.clear();
    if (m_hCommListenSocket) close(m_hCommListenSocket);
    if (m_hCommAcceptSocket) close(m_hCommAcceptSocket);
    m_hCommListenSocket = INVALID_SOCKET;
    m_hCommAcceptSocket = INVALID_SOCKET;
}

//===========================================================================

void CSuperSerialCard::CommTcpSerialAccept()
{
    if (m_hCommListenSocket != INVALID_SOCKET)
    {
        if (m_hCommAcceptSocket != INVALID_SOCKET){
            close(m_hCommAcceptSocket); // if reconnecting drop the existing
        }
        // Y: accept the connection
        m_hCommAcceptSocket = accept(m_hCommListenSocket, NULL, NULL);
    }
}

//===========================================================================

void CSuperSerialCard::CommTcpSerialReceive()
{

    if (m_hCommAcceptSocket != INVALID_SOCKET)
    {
        char Data;
        int nReceived = 0;
        int bytes_available = 1;
        bool empty;
        while(bytes_available && m_uRTS) // exit early on low RTS to allow TCP flow control
        {
            nReceived = (int)recv(m_hCommAcceptSocket, &Data, 1, 0);
            ((std::mutex*)m_CriticalSection)[CRIT_RECV].lock();
            m_qTcpSerialBuffer.push_back(Data);
            ((std::mutex*)m_CriticalSection)[CRIT_RECV].unlock();
            ioctl(m_hCommAcceptSocket, FIONREAD, &bytes_available);
        }
        ((std::mutex*)m_CriticalSection)[CRIT_RECV].lock();
        empty = m_qTcpSerialBuffer.empty();
        ((std::mutex*)m_CriticalSection)[CRIT_RECV].unlock();
        if (m_uRTS && m_bRxIrqEnabled && !empty)
        {
            CpuIrqAssert(IS_SSC);
            m_vbRxIrqPending = true;
        }
    }
}

//===========================================================================

BYTE __stdcall CSuperSerialCard::SSC_IORead(WORD PC, WORD uAddr, BYTE bWrite, BYTE uValue, ULONG nExecutedCycles)
{
    UINT uSlot = ((uAddr & 0xff) >> 4) - 8;
    CSuperSerialCard* pSSC = (CSuperSerialCard*) MemGetSlotParameters(uSlot);

    switch (uAddr & 0xf)
    {
    case 0x0:    return IO_Null(PC, uAddr, bWrite, uValue, nExecutedCycles);
    case 0x1:    return pSSC->CommDipSw(PC, uAddr, bWrite, uValue, nExecutedCycles);
    case 0x2:    return pSSC->CommDipSw(PC, uAddr, bWrite, uValue, nExecutedCycles);
    case 0x3:    return IO_Null(PC, uAddr, bWrite, uValue, nExecutedCycles);
    case 0x4:    return IO_Null(PC, uAddr, bWrite, uValue, nExecutedCycles);
    case 0x5:    return IO_Null(PC, uAddr, bWrite, uValue, nExecutedCycles);
    case 0x6:    return IO_Null(PC, uAddr, bWrite, uValue, nExecutedCycles);
    case 0x7:    return IO_Null(PC, uAddr, bWrite, uValue, nExecutedCycles);
    case 0x8:    return pSSC->CommReceive(PC, uAddr, bWrite, uValue, nExecutedCycles);
    case 0x9:    return pSSC->CommStatus(PC, uAddr, bWrite, uValue, nExecutedCycles);
    case 0xA:    return pSSC->CommCommand(PC, uAddr, bWrite, uValue, nExecutedCycles);
    case 0xB:    return pSSC->CommControl(PC, uAddr, bWrite, uValue, nExecutedCycles);
    case 0xC:    return IO_Null(PC, uAddr, bWrite, uValue, nExecutedCycles);
    case 0xD:    return IO_Null(PC, uAddr, bWrite, uValue, nExecutedCycles);
    case 0xE:    return IO_Null(PC, uAddr, bWrite, uValue, nExecutedCycles);
    case 0xF:    return IO_Null(PC, uAddr, bWrite, uValue, nExecutedCycles);
    }

    return 0;
}

BYTE __stdcall CSuperSerialCard::SSC_IOWrite(WORD PC, WORD uAddr, BYTE bWrite, BYTE uValue, ULONG nExecutedCycles)
{
    UINT uSlot = ((uAddr & 0xff) >> 4) - 8;
    CSuperSerialCard* pSSC = (CSuperSerialCard*) MemGetSlotParameters(uSlot);

    switch (uAddr & 0xf)
    {
    case 0x0:    return IO_Null(PC, uAddr, bWrite, uValue, nExecutedCycles);
    case 0x1:    return IO_Null(PC, uAddr, bWrite, uValue, nExecutedCycles);
    case 0x2:    return IO_Null(PC, uAddr, bWrite, uValue, nExecutedCycles);
    case 0x3:    return IO_Null(PC, uAddr, bWrite, uValue, nExecutedCycles);
    case 0x4:    return IO_Null(PC, uAddr, bWrite, uValue, nExecutedCycles);
    case 0x5:    return IO_Null(PC, uAddr, bWrite, uValue, nExecutedCycles);
    case 0x6:    return IO_Null(PC, uAddr, bWrite, uValue, nExecutedCycles);
    case 0x7:    return IO_Null(PC, uAddr, bWrite, uValue, nExecutedCycles);
    case 0x8:    return pSSC->CommTransmit(PC, uAddr, bWrite, uValue, nExecutedCycles);
    case 0x9:    return pSSC->CommProgramReset(PC, uAddr, bWrite, uValue, nExecutedCycles);
    case 0xA:    return pSSC->CommCommand(PC, uAddr, bWrite, uValue, nExecutedCycles);
    case 0xB:    return pSSC->CommControl(PC, uAddr, bWrite, uValue, nExecutedCycles);
    case 0xC:    return IO_Null(PC, uAddr, bWrite, uValue, nExecutedCycles);
    case 0xD:    return IO_Null(PC, uAddr, bWrite, uValue, nExecutedCycles);
    case 0xE:    return IO_Null(PC, uAddr, bWrite, uValue, nExecutedCycles);
    case 0xF:    return IO_Null(PC, uAddr, bWrite, uValue, nExecutedCycles);
    }

    return 0;
}

//===========================================================================

// 6551 ACIA Command Register ($C08A+s0)
// . EG. 0x09 = "no parity, enable IRQ" [Ref.2] - b7:5(No parity), b4 (No echo), b3:1(Enable TX,RX IRQs), b0(DTR: Enable receiver and all interrupts)
enum {    CMD_PARITY_MASK                = 3<<6,
        CMD_PARITY_ODD                = 0<<6,        // Odd parity
        CMD_PARITY_EVEN                = 1<<6,        // Even parity
        CMD_PARITY_MARK                = 2<<6,        // Mark parity
        CMD_PARITY_SPACE            = 3<<6,        // Space parity
        CMD_PARITY_ENA                = 1<<5,
        CMD_ECHO_MODE                = 1<<4,
        CMD_TX_MASK                    = 3<<2,
        CMD_TX_IRQ_DIS_RTS_HIGH        = 0<<2,
        CMD_TX_IRQ_ENA_RTS_LOW        = 1<<2,
        CMD_TX_IRQ_DIS_RTS_LOW        = 2<<2,
        CMD_TX_IRQ_DIS_RTS_LOW_BRK    = 3<<2,        // Transmit BRK
        CMD_RX_IRQ_DIS                = 1<<1,        // 1=IRQ interrupt disabled
        CMD_DTR                        = 1<<0,        // Data Terminal Ready: Enable(1) or disable(0) receiver and all interrupts (!DTR low)
};

BYTE __stdcall CSuperSerialCard::CommProgramReset(WORD, WORD, BYTE, BYTE, ULONG)
{
    // Command: top-3 parity bits unaffected
    UpdateCommandReg( m_uCommandByte & (CMD_PARITY_MASK|CMD_PARITY_ENA) );

    // Control: all bits unaffected
    // Status: all bits unaffects, except Overrun(bit2) is cleared

    return 0;
}

//===========================================================================

void CSuperSerialCard::UpdateCommandAndControlRegs(BYTE uCommandByte, BYTE uControlByte)
{
    // UpdateCommandReg() first to initialise m_uParity, before calling UpdateControlReg()
    UpdateCommandReg(uCommandByte);
    UpdateControlReg(uControlByte);
}

void CSuperSerialCard::UpdateCommandReg(BYTE command)
{
    m_uCommandByte = command;

    if (m_uCommandByte & CMD_PARITY_ENA)
    {
        switch (m_uCommandByte & CMD_PARITY_MASK)
        {
        case CMD_PARITY_ODD:    m_uParity = 1; break;
        case CMD_PARITY_EVEN:    m_uParity = 2; break;
        case CMD_PARITY_MARK:    m_uParity = 3; break;
        case CMD_PARITY_SPACE:    m_uParity = 4; break;
        }
    }
    else
    {
        m_uParity = 0;
    }

    if (m_uCommandByte & CMD_ECHO_MODE)        // Receiver mode echo (0=no echo, 1=echo)
    {
        _ASSERT(0);
        LogFileOutput("SSC: CommCommand(): unsupported Echo mode. Command=0x%02X\n", m_uCommandByte);
    }

    switch (m_uCommandByte & CMD_TX_MASK)    // transmitter interrupt control
    {
        // Note: the RTS signal must be set 'low' in order to receive any incoming data from the serial device [Ref.1]
        case CMD_TX_IRQ_DIS_RTS_HIGH:        // set RTS high and transmit no interrupts (transmitter is off [Ref.3])
            m_uRTS = 0;
            break;
        case CMD_TX_IRQ_ENA_RTS_LOW:        // set RTS low and transmit interrupts
            m_uRTS = 1;
            break;
        case CMD_TX_IRQ_DIS_RTS_LOW:        // set RTS low and transmit no interrupts
            m_uRTS = 1;
            break;
        case CMD_TX_IRQ_DIS_RTS_LOW_BRK:    // set RTS low and transmit break signals instead of interrupts
            m_uRTS = 1;
            _ASSERT(0);
            LogFileOutput("SSC: CommCommand(): unsupported TX mode. Command=0x%02X\n", m_uCommandByte);
            break;
    }
    ((std::mutex*)m_CriticalSection)[CRIT_RTS].try_lock();
    if (m_uRTS){
        ((std::mutex*)m_CriticalSection)[CRIT_RTS].unlock();
        //recv enabled RTS high
    }


    if (m_DIPSWCurrent.bInterrupts && m_uCommandByte & CMD_DTR)
    {
        // Assume enabling Rx IRQ if STATUS.ST_RX_FULL *does not* trigger an IRQ
        // . EG. Disable Rx IRQ, receive a byte (don't read STATUS or RX_DATA register), enable Rx IRQ
        // Assume enabling Tx IRQ if STATUS.ST_TX_EMPTY *does not* trigger an IRQ
        // . otherwise there'd be a "false" TX Empty IRQ even if nothing had ever been transferred!
        m_bTxIrqEnabled = (m_uCommandByte & CMD_TX_MASK) == CMD_TX_IRQ_ENA_RTS_LOW;
        m_bRxIrqEnabled = (m_uCommandByte & CMD_RX_IRQ_DIS) == 0;
    }
    else
    {
        m_bTxIrqEnabled = false;
        m_bRxIrqEnabled = false;
    }

    // Data Terminal Ready (DTR) setting (0=set DTR high (indicates 'not ready')) (GH#386)
    m_uDTR = (m_uCommandByte & CMD_DTR) ? 1 : 0;
    
    if (m_uRTS && m_bRxIrqEnabled && !m_qTcpSerialBuffer.empty())
    {
        CpuIrqAssert(IS_SSC);
        m_vbRxIrqPending = true;
    }
}

BYTE __stdcall CSuperSerialCard::CommCommand(WORD, WORD, BYTE write, BYTE value, ULONG)
{
    if (!CheckComm())
        return 0;

    if (write && (value    != m_uCommandByte))
    {
        UpdateCommandReg(value);
        UpdateCommState();
    }

    return m_uCommandByte;
}

//===========================================================================

void CSuperSerialCard::UpdateControlReg(BYTE control)
{
    m_uControlByte = control;

    // UPDATE THE BAUD RATE
    switch (m_uControlByte & 0x0F)
    {
        // Note that 1 MHz Apples (everything other than the Apple IIgs and //c
        // Plus running in "fast" mode) cannot handle 19.2 kbps, and even 9600
        // bps on these machines requires either some highly optimised code or
        // a decent buffer in the device being accessed.  The faster Apples
        // have no difficulty with this speed, however. [Ref.1]

        case 0x00: m_uBaudRate = B115200;    break;    // Internal clk: undoc'd 115.2K (or 16x external clock)
        case 0x01: // fall through [50 bps]
        case 0x02: // fall through [75 bps]
        case 0x03: // fall through [109.92 bps]
        case 0x04: // fall through [134.58 bps]
        case 0x05: m_uBaudRate = B110;        break;    // [150 bps]
        case 0x06: m_uBaudRate = B300;        break;
        case 0x07: m_uBaudRate = B600;        break;
        case 0x08: m_uBaudRate = B1200;        break;
        case 0x09: // fall through [1800 bps]
        case 0x0A: m_uBaudRate = B2400;        break;
        case 0x0B: // fall through [3600 bps]
        case 0x0C: m_uBaudRate = B4800;        break;
        case 0x0D: // fall through [7200 bps]
        case 0x0E: m_uBaudRate = B9600;        break;
        case 0x0F: m_uBaudRate = B19200;        break;
    }

    if (m_uControlByte & 0x10)
    {
        // receiver clock source [0= external, 1= internal]
    }

    // UPDATE THE BYTE SIZE
    switch (m_uControlByte & 0x60)
    {
        case 0x00: m_uByteSize = 8; break;
        case 0x20: m_uByteSize = 7; break;
        case 0x40: m_uByteSize = 6; break;
        case 0x60: m_uByteSize = 5; break;
    }

    // UPDATE THE NUMBER OF STOP BITS
    if (m_uControlByte & 0x80)
    {
        if ((m_uByteSize == 8) && (m_uParity != 0))
            m_uStopBits = 1;
        else if ((m_uByteSize == 5) && (m_uParity == 0))
            m_uStopBits = 1;
        else
            m_uStopBits = 2;
    }
    else
    {
        m_uStopBits = 1;
    }
}

BYTE __stdcall CSuperSerialCard::CommControl(WORD, WORD, BYTE write, BYTE value, ULONG)
{
    if (!CheckComm())
        return 0;

    if (write && (value != m_uControlByte))
    {
        UpdateControlReg(value);
        UpdateCommState();
    }

    return m_uControlByte;
}

//===========================================================================

BYTE __stdcall CSuperSerialCard::CommReceive(WORD, WORD, BYTE, BYTE, ULONG)
{
    if (!CheckComm())
        return 0;

    BYTE result = 0;
    const std::lock_guard<std::mutex> lock(((std::mutex*)m_CriticalSection)[CRIT_RECV]);

    if (!m_uRTS){
        //printf("CommReceive but RTS disable. (queue size: %d)\n", m_qTcpSerialBuffer.size());
    }
    if (!m_qTcpSerialBuffer.empty())
    {
        result = m_qTcpSerialBuffer.front();
        m_qTcpSerialBuffer.pop_front();

        if (m_uRTS && m_bRxIrqEnabled && !m_qTcpSerialBuffer.empty())
        {
            CpuIrqAssert(IS_SSC);
            m_vbRxIrqPending = true;
        }
    }
    

    return result;
}

//===========================================================================

void CSuperSerialCard::TransmitDone(void)
{

    _ASSERT(m_vbTxEmpty == false);
    m_vbTxEmpty = true;    // Transmit done (TCP)

    if (m_bTxIrqEnabled)    // GH#522
    {
        CpuIrqAssert(IS_SSC);
        m_vbTxIrqPending = true;
    }
}

BYTE __stdcall CSuperSerialCard::CommTransmit(WORD, WORD, BYTE, BYTE value, ULONG)
{
    if (!CheckComm())
        return 0;

    // If transmitter is disabled then: Is data just discarded or does it get transmitted if transmitter is later enabled?
    //if ((m_uCommandByte & CMD_TX_MASK) == CMD_TX_IRQ_DIS_RTS_HIGH)    // Transmitter disable, so just discard for now
    //    return 0;

    if (m_hCommAcceptSocket != INVALID_SOCKET)
    {
        BYTE data = value;
        if (m_uByteSize < 8)
        {
            data &= ~(1 << m_uByteSize);
        }
        int sent = (int)send(m_hCommAcceptSocket, (const char*)&data, 1, 0);
        //printf("SENT: %02x\n", (unsigned)data);
        _ASSERT(sent == 1);
        if (sent == 1)
        {
            m_vbTxEmpty = false;
            // Assume that send() completes immediately
            TransmitDone();
        }
    }
    else
    {
        LogFileOutput("SSC: CommTransmit(): WriteFile() failed: m_hCommAcceptSocket NULL\n");
    }

    return 0;
}

//===========================================================================

// 6551 ACIA Status Register ($C089+s0)
// ------------------------------------
// Bit     Value     Meaning
// 7    1       Interrupt (IRQ) true (cleared by reading status reg [Ref.3])
// 6    0       Data Set Ready (DSR) true [0=DSR low (ready), 1=DSR high (not ready)]
// 5    0       Data Carrier Detect (DCD) true [0=DCD low (detected), 1=DCD high (not detected)]
// 4    1       Transmit register empty
// 3    1       Receive register full
// 2    1       Overrun error
// 1    1       Framing error
// 0    1       Parity error

enum {    ST_IRQ            = 1<<7,
        ST_DSR            = 1<<6,
        ST_DCD            = 1<<5,
        ST_TX_EMPTY        = 1<<4,
        ST_RX_FULL        = 1<<3,
        ST_OVERRUN_ERR    = 1<<2,
        ST_FRAMING_ERR    = 1<<1,
        ST_PARITY_ERR    = 1<<0,
};

BYTE __stdcall CSuperSerialCard::CommStatus(WORD, WORD, BYTE, BYTE, ULONG)
{
    if (!CheckComm())
        return ST_DSR | ST_DCD | ST_TX_EMPTY;

    DWORD modemStatus = m_kDefaultModemStatus;

    if (m_hCommListenSocket != INVALID_SOCKET && m_hCommAcceptSocket != INVALID_SOCKET)
    {
        modemStatus = 7;//FIXME MS_RLSD_ON | MS_DSR_ON | MS_CTS_ON;
    }

    //

    bool bComSerialBufferEmpty = true;    // Assume true, so if using TCP then logic below works
    ((std::mutex*)m_CriticalSection)[CRIT_RECV].lock();
    if (m_hCommHandle != INVALID_HANDLE_VALUE)
    {
        const UINT uSSCIdx = m_vuRxCurrBuffer ^ 1;
        bComSerialBufferEmpty = m_qComSerialBuffer[uSSCIdx].empty();
    }

    BYTE IRQ = 0;
    if (m_bTxIrqEnabled)
    {
        IRQ |= m_vbTxIrqPending ? ST_IRQ : 0;
        m_vbTxIrqPending = false;    // Ensure 2 reads of STATUS reg only return ST_IRQ for first read
    }
    if (m_bRxIrqEnabled)
    {
        IRQ |= m_vbRxIrqPending ? ST_IRQ : 0;
        m_vbRxIrqPending = false;    // Ensure 2 reads of STATUS reg only return ST_IRQ for first read
    }

    //

    BYTE DSR = (modemStatus & MS_DSR_ON)  ? 0x00 : ST_DSR;    // DSR is active low (see SY6551 datasheet) (GH#386)
    BYTE DCD = (modemStatus & MS_RLSD_ON) ? 0x00 : ST_DCD;    // DCD is active low (see SY6551 datasheet) (GH#386)

    //

    BYTE TX_EMPTY = m_vbTxEmpty ? ST_TX_EMPTY : 0;
    BYTE RX_FULL  = (!m_qTcpSerialBuffer.empty()) ? ST_RX_FULL : 0;

    //

    BYTE uStatus =
          IRQ
        | DSR
        | DCD
        | TX_EMPTY
        | RX_FULL;

    ((std::mutex*)m_CriticalSection)[CRIT_RECV].unlock();

    CpuIrqDeassert(IS_SSC);        // Read status reg always clears IRQ

    return uStatus;
}

//===========================================================================

// NB. Some DIPSW settings can't be read:
// SSC-47: Three switches are not connected to the LS365s:
// . SW2-6: passes interrupt requests from ACIA to the Apple II
// . SW1-7 ON and SW2-7 OFF: connects DCD to the DCD input of the ACIA
// . SW1-7 OFF and SW2-7 ON: splices SCTS to the DCD input of the ACIA (when jumper is in TERMINAL position)
BYTE __stdcall CSuperSerialCard::CommDipSw(WORD, WORD addr, BYTE, BYTE, ULONG)
{
    BYTE sw = 0;

    switch (addr & 0xf)
    {
    case 1:    // DIPSW1
        sw = (BaudRateToIndex(m_DIPSWCurrent.uBaudRate)<<4) | m_DIPSWCurrent.eFirmwareMode;
        break;

    case 2:    // DIPSW2
        // Comms mode: SSC-23
        BYTE SW2_1 = m_DIPSWCurrent.uStopBits == 2 ? 1 : 0;    // SW2-1 (Stop bits: 1-ON(0); 2-OFF(1))
        BYTE SW2_2 = m_DIPSWCurrent.uByteSize == 7 ? 1 : 0;                // SW2-2 (Data bits: 8-ON(0); 7-OFF(1))

        // SW2-3 (Parity: odd-ON(0); even-OFF(1))
        // SW2-4 (Parity: none-ON(0); SW2-3 don't care)
        BYTE SW2_3,SW2_4;
        switch (m_DIPSWCurrent.uParity)
        {
        case 1:
            SW2_3 = 0; SW2_4 = 1;
            break;
        case 2:
            SW2_3 = 1; SW2_4 = 1;
            break;
        default:
            _ASSERT(0);
            // fall through...
        case 0:
            SW2_3 = 0; SW2_4 = 0;
            break;
        }

        BYTE SW2_5 = m_DIPSWCurrent.bLinefeed ? 0 : 1;                    // SW2-5 (LF: yes-ON(0); no-OFF(1))

        BYTE CTS = 1;    // Default to CTS being false. (Support CTS in DIPSW: GH#311)
        if (CheckComm() && m_hCommHandle != INVALID_HANDLE_VALUE)
            CTS = (m_dwModemStatus & MS_CTS_ON) ? 0 : 1;    // CTS active low (see SY6551 datasheet)
        else if (m_hCommListenSocket != INVALID_SOCKET)
            CTS = (m_hCommAcceptSocket != INVALID_SOCKET) ? 0 : 1;

        // SSC-54:
        sw =    SW2_1<<7 |    // b7 : SW2-1
                    0<<6 |    // b6 : -
                SW2_2<<5 |    // b5 : SW2-2
                    0<<4 |    // b4 : -
                SW2_3<<3 |    // b3 : SW2-3
                SW2_4<<2 |    // b2 : SW2-4
                SW2_5<<1 |    // b1 : SW2-5
                  CTS<<0;    // b0 : CTS
        break;
    }

    return sw;
}

//===========================================================================

void CSuperSerialCard::InitializeIO(LPBYTE pCxRomPeripheral)
{
    const UINT SSC_FW_SIZE = 2*1024;
    const UINT SSC_SLOT_FW_SIZE = 256;
    const UINT SSC_SLOT_FW_OFFSET = 7*256;

    BYTE* pData = GetFrame().GetResource(IDR_SSC_FW, "FIRMWARE", SSC_FW_SIZE);
    if(pData == NULL)
        return;

    memcpy(pCxRomPeripheral + m_slot*SSC_SLOT_FW_SIZE, pData+SSC_SLOT_FW_OFFSET, SSC_SLOT_FW_SIZE);

    // Expansion ROM
    if (m_pExpansionRom == NULL)
    {
        m_pExpansionRom = new BYTE [SSC_FW_SIZE];
        memcpy(m_pExpansionRom, pData, SSC_FW_SIZE);
    }

    RegisterIoHandler(m_slot, &CSuperSerialCard::SSC_IORead, &CSuperSerialCard::SSC_IOWrite, NULL, NULL, this, m_pExpansionRom);
}

//===========================================================================

void CSuperSerialCard::Reset(const bool /* powerCycle */)
{
    CloseComm();
    InternalReset();
}

//===========================================================================

// dwNewSerialPortItem is the drop-down list item
void CSuperSerialCard::CommSetSerialPort(DWORD dwNewSerialPortItem)
{
    if (m_dwSerialPortItem == dwNewSerialPortItem)
        return;

    _ASSERT(!IsActive());
    if (IsActive())
        return;

    m_dwSerialPortItem = dwNewSerialPortItem;

    if (m_dwSerialPortItem == m_uTCPChoiceItemIdx)
    {
        m_currentSerialPortName = TEXT_SERIAL_TCP;
    }
    else
    {
        m_currentSerialPortName.clear();    // "None"
    }

    SetRegistrySerialPortName();
}

//===========================================================================

void CSuperSerialCard::CheckCommEvent(DWORD dwEvtMask)
{
}

//CommThread accepts socket and recvs data. Data sending happens in main thread.
DWORD WINAPI CSuperSerialCard::CommThread(LPVOID lpParameter)
{
    char c;
    int bytes_available;
    CSuperSerialCard* pSSC = (CSuperSerialCard*) lpParameter;
    while (pSSC->m_hCommListenSocket != INVALID_SOCKET){
        pSSC->CommTcpSerialAccept();
        while(recv(pSSC->m_hCommAcceptSocket, &c, 1, MSG_PEEK) > 0){
            do {
                pSSC->CommTcpSerialReceive();
                ((std::mutex*)pSSC->m_CriticalSection)[CRIT_RTS].lock(); // held if RTS low
                ((std::mutex*)pSSC->m_CriticalSection)[CRIT_RTS].unlock();
                ioctl(pSSC->m_hCommAcceptSocket, FIONREAD, &bytes_available);
            } while (bytes_available);
        }
        close(pSSC->m_hCommAcceptSocket);
        pSSC->m_hCommAcceptSocket = INVALID_SOCKET;
    }
    //pSSC->CheckCommEvent(dwEvtMask);
    return 0;
}

bool CSuperSerialCard::CommThInit()
{
    if (m_hCommThread == NULL){
        std::thread t(&CSuperSerialCard::CommThread, this);
        t.detach();
        m_hCommThread = (HANDLE)(&t);
    }
    return true;
}

void CSuperSerialCard::CommThUninit()
{
    std::thread *pt = (std::thread *)m_hCommThread;
    close(m_hCommListenSocket); // will exit thread waiting on accept()
    ((std::mutex*)m_CriticalSection)[CRIT_RTS].try_lock();
    ((std::mutex*)m_CriticalSection)[CRIT_RTS].unlock();
    m_hCommListenSocket = INVALID_SOCKET;
    if (pt != NULL){
        m_hCommThread = NULL;
    }
}

//===========================================================================

void CSuperSerialCard::ScanCOMPorts()
{
    m_uTCPChoiceItemIdx = 0;
}

std::string const& CSuperSerialCard::GetSerialPortChoices()
{
    if (IsActive())
        return m_strSerialPortChoices;

    m_strSerialPortChoices += "TCP";
    m_strSerialPortChoices += '\0'; // NULL char for combo box selection.
    // std::string()'s implicit nul terminator becomes combo box end of list marker
    return m_strSerialPortChoices;
}

// Called by ctor & LoadSnapshot()
void CSuperSerialCard::SetSerialPortName(const char* pSerialPortName)
{
    m_currentSerialPortName = pSerialPortName;

    // Init m_aySerialPortChoices, so that we have choices to show if serial is active when we 1st open Config dialog
    GetSerialPortChoices();

    if (strncmp(TEXT_SERIAL_TCP, pSerialPortName, sizeof(TEXT_SERIAL_TCP)-1) == 0)
    {
        m_dwSerialPortItem = m_uTCPChoiceItemIdx;
    }
    else
    {
        m_currentSerialPortName.clear();    // "None"
        m_dwSerialPortItem = 0;
    }
}

void CSuperSerialCard::SetRegistrySerialPortName(void)
{
}

//===========================================================================

// Unit version history:
// 2: Added: Support DCD flag
//    Removed: redundant data (encapsulated in Command & Control bytes)
static const UINT kUNIT_VERSION = 2;

#define SS_YAML_VALUE_CARD_SSC "Super Serial Card"

#define SS_YAML_KEY_DIPSWDEFAULT "DIPSW Default"
#define SS_YAML_KEY_DIPSWCURRENT "DIPSW Current"

#define SS_YAML_KEY_BAUDRATE "Baud Rate"
#define SS_YAML_KEY_FWMODE "Firmware mode"
#define SS_YAML_KEY_STOPBITS "Stop Bits"
#define SS_YAML_KEY_BYTESIZE "Byte Size"
#define SS_YAML_KEY_PARITY "Parity"
#define SS_YAML_KEY_LINEFEED "Linefeed"
#define SS_YAML_KEY_INTERRUPTS "Interrupts"
#define SS_YAML_KEY_CONTROL "Control Byte"
#define SS_YAML_KEY_COMMAND "Command Byte"
#define SS_YAML_KEY_INACTIVITY "Comm Inactivity"
#define SS_YAML_KEY_TXIRQENABLED "TX IRQ Enabled"
#define SS_YAML_KEY_RXIRQENABLED "RX IRQ Enabled"
#define SS_YAML_KEY_TXIRQPENDING "TX IRQ Pending"
#define SS_YAML_KEY_RXIRQPENDING "RX IRQ Pending"
#define SS_YAML_KEY_WRITTENTX "Written TX"
#define SS_YAML_KEY_SERIALPORTNAME "Serial Port Name"
#define SS_YAML_KEY_SUPPORT_DCD "Support DCD"

const std::string& CSuperSerialCard::GetSnapshotCardName(void)
{
    static const std::string name(SS_YAML_VALUE_CARD_SSC);
    return name;
}

void CSuperSerialCard::SaveSnapshotDIPSW(YamlSaveHelper& yamlSaveHelper, std::string key, SSC_DIPSW& dipsw)
{
    YamlSaveHelper::Label label(yamlSaveHelper, "%s:\n", key.c_str());
    yamlSaveHelper.SaveUint(SS_YAML_KEY_BAUDRATE, dipsw.uBaudRate);
    yamlSaveHelper.SaveUint(SS_YAML_KEY_FWMODE, dipsw.eFirmwareMode);
    yamlSaveHelper.SaveUint(SS_YAML_KEY_STOPBITS, dipsw.uStopBits);
    yamlSaveHelper.SaveUint(SS_YAML_KEY_BYTESIZE, dipsw.uByteSize);
    yamlSaveHelper.SaveUint(SS_YAML_KEY_PARITY, dipsw.uParity);
    yamlSaveHelper.SaveBool(SS_YAML_KEY_LINEFEED, dipsw.bLinefeed);
    yamlSaveHelper.SaveBool(SS_YAML_KEY_INTERRUPTS, dipsw.bInterrupts);
}

void CSuperSerialCard::SaveSnapshot(YamlSaveHelper& yamlSaveHelper)
{
    YamlSaveHelper::Slot slot(yamlSaveHelper, GetSnapshotCardName(), m_slot, kUNIT_VERSION);

    YamlSaveHelper::Label unit(yamlSaveHelper, "%s:\n", SS_YAML_KEY_STATE);
    SaveSnapshotDIPSW(yamlSaveHelper, SS_YAML_KEY_DIPSWDEFAULT, m_DIPSWDefault);
    SaveSnapshotDIPSW(yamlSaveHelper, SS_YAML_KEY_DIPSWCURRENT, m_DIPSWCurrent);
    yamlSaveHelper.SaveHexUint8(SS_YAML_KEY_CONTROL, m_uControlByte);
    yamlSaveHelper.SaveHexUint8(SS_YAML_KEY_COMMAND, m_uCommandByte);
    yamlSaveHelper.SaveBool(SS_YAML_KEY_TXIRQPENDING, m_vbTxIrqPending);
    yamlSaveHelper.SaveBool(SS_YAML_KEY_RXIRQPENDING, m_vbRxIrqPending);
    yamlSaveHelper.SaveBool(SS_YAML_KEY_WRITTENTX, m_vbTxEmpty);
    yamlSaveHelper.SaveBool(SS_YAML_KEY_SUPPORT_DCD, m_bCfgSupportDCD);
    yamlSaveHelper.SaveString(SS_YAML_KEY_SERIALPORTNAME, GetSerialPortName());
}

void CSuperSerialCard::LoadSnapshotDIPSW(YamlLoadHelper& yamlLoadHelper, std::string key, SSC_DIPSW& dipsw)
{
    if (!yamlLoadHelper.GetSubMap(key))
        throw std::runtime_error("Card: Expected key: " + key);

    dipsw.uBaudRate        = yamlLoadHelper.LoadUint(SS_YAML_KEY_BAUDRATE);
    dipsw.eFirmwareMode = (eFWMODE) yamlLoadHelper.LoadUint(SS_YAML_KEY_FWMODE);
    dipsw.uStopBits        = yamlLoadHelper.LoadUint(SS_YAML_KEY_STOPBITS);
    dipsw.uByteSize        = yamlLoadHelper.LoadUint(SS_YAML_KEY_BYTESIZE);
    dipsw.uParity        = yamlLoadHelper.LoadUint(SS_YAML_KEY_PARITY);
    dipsw.bLinefeed        = yamlLoadHelper.LoadBool(SS_YAML_KEY_LINEFEED);
    dipsw.bInterrupts    = yamlLoadHelper.LoadBool(SS_YAML_KEY_INTERRUPTS);

    yamlLoadHelper.PopMap();
}

bool CSuperSerialCard::LoadSnapshot(YamlLoadHelper& yamlLoadHelper, UINT version)
{
    if (version < 1 || version > kUNIT_VERSION)
        ThrowErrorInvalidVersion(version);

    LoadSnapshotDIPSW(yamlLoadHelper, SS_YAML_KEY_DIPSWDEFAULT, m_DIPSWDefault);
    LoadSnapshotDIPSW(yamlLoadHelper, SS_YAML_KEY_DIPSWCURRENT, m_DIPSWCurrent);

    if (version == 1)    // Consume redundant/obsolete data
    {
        yamlLoadHelper.LoadUint(SS_YAML_KEY_PARITY);        // Redundant: derived from uCommandByte in UpdateCommandReg()
        yamlLoadHelper.LoadBool(SS_YAML_KEY_TXIRQENABLED);    // Redundant: derived from uCommandByte in UpdateCommandReg()
        yamlLoadHelper.LoadBool(SS_YAML_KEY_RXIRQENABLED);    // Redundant: derived from uCommandByte in UpdateCommandReg()

        yamlLoadHelper.LoadUint(SS_YAML_KEY_BAUDRATE);        // Redundant: derived from uControlByte in UpdateControlReg()
        yamlLoadHelper.LoadUint(SS_YAML_KEY_STOPBITS);        // Redundant: derived from uControlByte in UpdateControlReg()
        yamlLoadHelper.LoadUint(SS_YAML_KEY_BYTESIZE);        // Redundant: derived from uControlByte in UpdateControlReg()

        yamlLoadHelper.LoadUint(SS_YAML_KEY_INACTIVITY);    // Obsolete (so just consume)
    }
    else if (version >= 2)
    {
        SupportDCD( yamlLoadHelper.LoadBool(SS_YAML_KEY_SUPPORT_DCD) );
    }

    UINT uCommandByte    = yamlLoadHelper.LoadUint(SS_YAML_KEY_COMMAND);
    UINT uControlByte    = yamlLoadHelper.LoadUint(SS_YAML_KEY_CONTROL);
    UpdateCommandAndControlRegs(uCommandByte, uControlByte);

    m_vbTxIrqPending    = yamlLoadHelper.LoadBool(SS_YAML_KEY_TXIRQPENDING);
    m_vbRxIrqPending    = yamlLoadHelper.LoadBool(SS_YAML_KEY_RXIRQPENDING);
    m_vbTxEmpty            = yamlLoadHelper.LoadBool(SS_YAML_KEY_WRITTENTX);

    if (m_vbTxIrqPending || m_vbRxIrqPending)    // GH#677
        CpuIrqAssert(IS_SSC);

    std::string serialPortName = yamlLoadHelper.LoadString(SS_YAML_KEY_SERIALPORTNAME);
    SetSerialPortName(serialPortName.c_str());
    SetRegistrySerialPortName();

    return true;
}
