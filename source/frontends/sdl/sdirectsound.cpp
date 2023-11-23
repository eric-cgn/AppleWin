#include "StdAfx.h"
#include "frontends/sdl/sdirectsound.h"

#include "windows.h"
#include "linux/linuxinterface.h"

#include "SoundCore.h"

#ifndef USE_COREAUDIO
#include <SDL.h>
#else
#include <AudioToolbox/AudioToolbox.h>
#endif // USE_COREAUDIO

#include <unordered_map>
#include <memory>
#include <iostream>
#include <iomanip>

namespace
{

#ifdef USE_COREAUDIO
OSStatus DirectSoundRenderProc(void * inRefCon,
                               AudioUnitRenderActionFlags * ioActionFlags,
                               const AudioTimeStamp * inTimeStamp,
                               UInt32 inBusNumber,
                               UInt32 inNumberFrames,
                               AudioBufferList * ioData);
#else
  size_t getBytesPerSecond(const SDL_AudioSpec & spec)
  {
    const size_t bitsPerSample = spec.format & SDL_AUDIO_MASK_BITSIZE;
    const size_t bytesPerFrame = spec.channels * bitsPerSample / 8;
    return spec.freq * bytesPerFrame;
  }

  size_t nextPowerOf2(size_t n)
  {
    size_t k = 1;
    while (k < n)
      k *= 2;
    return k;
  }

  void printAudioDeviceErrorOnce()
  {
    static bool once = false;
    if (!once)
    {
      std::cerr << "SDL_OpenAudioDevice: " << SDL_GetError() << std::endl;
      once = true;
    }
  }
#endif // USE_COREAUDIO

  class DirectSoundGenerator
  {
  public:
    DirectSoundGenerator(IDirectSoundBuffer * buffer);
    ~DirectSoundGenerator();

    void stop();
    void writeAudio(const char * deviceName, const size_t ms);
    void resetUnderruns();

    void printInfo() const;
    sa2::SoundInfo getInfo() const;

#ifdef USE_COREAUDIO
    friend OSStatus DirectSoundRenderProc(void * inRefCon,
                                          AudioUnitRenderActionFlags * ioActionFlags,
                                          const AudioTimeStamp * inTimeStamp,
                                          UInt32 inBusNumber,
                                          UInt32 inNumberFrames,
                                          AudioBufferList * ioData);
    void setVolumeIfNecessary();
#endif // USE_COREAUDIO

  private:
#ifndef USE_COREAUDIO
    static void staticAudioCallback(void* userdata, uint8_t* stream, int len);

    void audioCallback(uint8_t* stream, int len);
#endif // USE_COREAUDIO

    IDirectSoundBuffer * myBuffer;

#ifndef USE_COREAUDIO
    std::vector<uint8_t> myMixerBuffer;

    SDL_AudioDeviceID myAudioDevice;
    SDL_AudioSpec myAudioSpec;
#else
    std::vector<uint8_t> myMixerBuffer;

    AudioUnit outputUnit;
    Float32 volume;
#endif // USE_COREAUDIO

    size_t myBytesPerSecond;

    void close();
    bool isRunning() const;

#ifndef USE_COREAUDIO
    uint8_t * mixBufferTo(uint8_t * stream);
#endif
  };

  std::unordered_map<IDirectSoundBuffer *, std::shared_ptr<DirectSoundGenerator>> activeSoundGenerators;

#ifndef USE_COREAUDIO
  void DirectSoundGenerator::staticAudioCallback(void* userdata, uint8_t* stream, int len)
  {
    DirectSoundGenerator * generator = static_cast<DirectSoundGenerator *>(userdata);
    return generator->audioCallback(stream, len);
  }

  void DirectSoundGenerator::audioCallback(uint8_t* stream, int len)
  {
    LPVOID lpvAudioPtr1, lpvAudioPtr2;
    DWORD dwAudioBytes1, dwAudioBytes2;
    const size_t bytesRead = myBuffer->Read(len, &lpvAudioPtr1, &dwAudioBytes1, &lpvAudioPtr2, &dwAudioBytes2);

    myMixerBuffer.resize(bytesRead);

    uint8_t * dest = myMixerBuffer.data();
    if (lpvAudioPtr1 && dwAudioBytes1)
    {
      memcpy(dest, lpvAudioPtr1, dwAudioBytes1);
      dest += dwAudioBytes1;
    }
    if (lpvAudioPtr2 && dwAudioBytes2)
    {
      memcpy(dest, lpvAudioPtr2, dwAudioBytes2);
      dest += dwAudioBytes2;
    }

    stream = mixBufferTo(stream);

    const size_t gap = len - bytesRead;
    if (gap)
    {
      memset(stream, myAudioSpec.silence, gap);
    }
  }
#endif // USE_COREAUDIO

  DirectSoundGenerator::DirectSoundGenerator(IDirectSoundBuffer * buffer)
    : myBuffer(buffer)
#ifndef USE_COREAUDIO
    , myAudioDevice(0)
#else
    , outputUnit(0)
    , volume(0)
#endif
    , myBytesPerSecond(0)
  {
#ifndef USE_COREAUDIO
    SDL_zero(myAudioSpec);
#else
    AudioComponentDescription desc = { 0 };
    desc.componentType = kAudioUnitType_Output;
    desc.componentSubType = kAudioUnitSubType_DefaultOutput;
    desc.componentManufacturer = kAudioUnitManufacturer_Apple;
    
    AudioComponent comp = AudioComponentFindNext(NULL, &desc);
    if (comp == NULL)
    {
      fprintf(stderr, "can't find audio component\n");
      return;
    }
    
    if (AudioComponentInstanceNew(comp, &outputUnit) != noErr)
    {
      fprintf(stderr, "can't create output unit\n");
      return;
    }
    
    AudioStreamBasicDescription absd = { 0 };
    absd.mSampleRate = myBuffer->sampleRate;
    absd.mFormatID = kAudioFormatLinearPCM;
    absd.mFormatFlags = kAudioFormatFlagIsSignedInteger;
    absd.mFramesPerPacket = 1;
    absd.mChannelsPerFrame = (UInt32)myBuffer->channels;
    absd.mBitsPerChannel = sizeof(SInt16) * CHAR_BIT;
    absd.mBytesPerPacket = sizeof(SInt16) * (UInt32)myBuffer->channels;
    absd.mBytesPerFrame = sizeof(SInt16) * (UInt32)myBuffer->channels;
    if (AudioUnitSetProperty(outputUnit,
                             kAudioUnitProperty_StreamFormat,
                             kAudioUnitScope_Input,
                             0,
                             &absd,
                             sizeof(absd))) {
      fprintf(stderr, "can't set stream format\n");
      return;
    }
    
    AURenderCallbackStruct input;
    input.inputProc = DirectSoundRenderProc;
    input.inputProcRefCon = this;
    if (AudioUnitSetProperty(outputUnit,
                             kAudioUnitProperty_SetRenderCallback,
                             kAudioUnitScope_Input,
                             0,
                             &input,
                             sizeof(input)) != noErr)
    {
      fprintf(stderr, "can't set callback property\n");
      return;
    }
    
    setVolumeIfNecessary();
    
    if (AudioUnitInitialize(outputUnit) != noErr)
    {
      fprintf(stderr, "can't initialize output unit\n");
      return;
    }
    
    OSStatus status = AudioOutputUnitStart(outputUnit);
    fprintf(stderr, "output unit %p, status %d\n", outputUnit, status);
#endif
  }

  DirectSoundGenerator::~DirectSoundGenerator()
  {
    close();
  }

  void DirectSoundGenerator::close()
  {
#ifndef USE_COREAUDIO
    SDL_CloseAudioDevice(myAudioDevice);
    myAudioDevice = 0;
#else
    AudioOutputUnitStop(outputUnit);
    AudioUnitUninitialize(outputUnit);
    AudioComponentInstanceDispose(outputUnit);
    outputUnit = 0;
#endif // USE_COREAUDIO
  }

  bool DirectSoundGenerator::isRunning() const
  {
#ifndef USE_COREAUDIO
    return myAudioDevice;
#else
    return outputUnit;
#endif
  }

  void DirectSoundGenerator::printInfo() const
  {
    if (isRunning())
    {
#ifndef USE_COREAUDIO
      const DWORD bytesInBuffer = myBuffer->GetBytesInBuffer();
      std::cerr << "Channels: " << (int)myAudioSpec.channels;
      std::cerr << ", buffer: " << std::setw(6) << bytesInBuffer;
      const double time = double(bytesInBuffer) / myBytesPerSecond * 1000;
      std::cerr << ", " << std::setw(8) << time << " ms";
      std::cerr << ", underruns: " << std::setw(10) << myBuffer->GetBufferUnderruns() << std::endl;
#endif // USE_COREAUDIO
    }
  }

  sa2::SoundInfo DirectSoundGenerator::getInfo() const
  {
    // FIXME: The #ifdef'ed out bits probably need to be restored to use CoreAudio in sa2.
    
    sa2::SoundInfo info;
    info.running = isRunning();
#ifndef USE_COREAUDIO
    info.channels = myAudioSpec.channels;
#endif
    info.volume = myBuffer->GetLogarithmicVolume();
    info.numberOfUnderruns = myBuffer->GetBufferUnderruns();

    if (info.running && myBytesPerSecond > 0)
    {
      const DWORD bytesInBuffer = myBuffer->GetBytesInBuffer();
      const float coeff = 1.0 / myBytesPerSecond;
      info.buffer = bytesInBuffer * coeff;
      info.size = myBuffer->bufferSize * coeff;
    }

    return info;
  }

  void DirectSoundGenerator::resetUnderruns()
  {
    myBuffer->ResetUnderrruns();
  }

  void DirectSoundGenerator::stop()
  {
#ifndef USE_COREAUDIO
    if (myAudioDevice)
#else
    if (outputUnit)
#endif // USE_COREAUDIO
    {
#ifndef USE_COREAUDIO
      SDL_PauseAudioDevice(myAudioDevice, 1);
#endif
      close();
    }
  }

#ifndef USE_COREAUDIO
  uint8_t * DirectSoundGenerator::mixBufferTo(uint8_t * stream)
  {
    // we could copy ADJUST_VOLUME from SDL_mixer.c and avoid all copying and (rare) race conditions
    const double logVolume = myBuffer->GetLogarithmicVolume();
    // same formula as QAudio::convertVolume()
    const double linVolume = logVolume > 0.99 ? 1.0 : -std::log(1.0 - logVolume) / std::log(100.0);
    const uint8_t svolume = uint8_t(linVolume * SDL_MIX_MAXVOLUME);

    const size_t len = myMixerBuffer.size();
    memset(stream, 0, len);
    SDL_MixAudioFormat(stream, myMixerBuffer.data(), myAudioSpec.format, len, svolume);
    return stream + len;
  }
#endif // USE_COREAUDIO

  void DirectSoundGenerator::writeAudio(const char * deviceName, const size_t ms)
  {
#ifndef USE_COREAUDIO
    // this is autostart as we only do for the palying buffers
    // and AW might activate one later
    if (myAudioDevice)
    {
      return;
    }

    DWORD dwStatus;
    myBuffer->GetStatus(&dwStatus);
    if (!(dwStatus & DSBSTATUS_PLAYING))
    {
      return;
    }

    SDL_AudioSpec want;
    SDL_zero(want);

    want.freq = myBuffer->sampleRate;
    want.format = AUDIO_S16LSB;
    want.channels = myBuffer->channels;
    want.samples = std::min<size_t>(MAX_SAMPLES, nextPowerOf2(myBuffer->sampleRate * ms / 1000));
    want.callback = staticAudioCallback;
    want.userdata = this;
    myAudioDevice = SDL_OpenAudioDevice(deviceName, 0, &want, &myAudioSpec, 0);

    if (myAudioDevice)
    {
      myBytesPerSecond = getBytesPerSecond(myAudioSpec);

      SDL_PauseAudioDevice(myAudioDevice, 0);
    }
    else
    {
      printAudioDeviceErrorOnce();
    }
#endif // USE_COREAUDIO
  }

#ifdef USE_COREAUDIO

  void DirectSoundGenerator::setVolumeIfNecessary()
  {
    const double logVolume = myBuffer->GetLogarithmicVolume();
    // same formula as QAudio::convertVolume()
    const Float32 linVolume = logVolume > 0.99 ? 1.0 : -std::log(1.0 - logVolume) / std::log(100.0);
    if (fabs(linVolume - volume) > FLT_EPSILON) {
      if (AudioUnitSetParameter(outputUnit,
                                kHALOutputParam_Volume,
                                kAudioUnitScope_Global,
                                0,
                                linVolume,
                                0) == noErr)
      {
        volume = linVolume;
      }
      else
      {
        fprintf(stderr, "can't set volume\n");
      }
    }
  }

  OSStatus DirectSoundRenderProc(void * inRefCon,
                                 AudioUnitRenderActionFlags * ioActionFlags,
                                 const AudioTimeStamp * inTimeStamp,
                                 UInt32 inBusNumber,
                                 UInt32 inNumberFrames,
                                 AudioBufferList * ioData)
  {
    DirectSoundGenerator *dsg = (DirectSoundGenerator *)inRefCon;
    UInt8 * data = (UInt8 *)ioData->mBuffers[0].mData;
    
    DWORD size = (DWORD)(inNumberFrames * dsg->myBuffer->channels * sizeof(SInt16));
    
    LPVOID lpvAudioPtr1, lpvAudioPtr2;
    DWORD dwAudioBytes1, dwAudioBytes2;
    dsg->myBuffer->Read(size,
                        &lpvAudioPtr1,
                        &dwAudioBytes1,
                        &lpvAudioPtr2,
                        &dwAudioBytes2);
    
    // copy the first part from the ring buffer
    if (lpvAudioPtr1 && dwAudioBytes1)
    {
      memcpy(data, lpvAudioPtr1, dwAudioBytes1);
    }
    // copy the second (wrapped-around) part of the ring buffer, if any
    if (lpvAudioPtr2 && dwAudioBytes2)
    {
      memcpy(data + dwAudioBytes1, lpvAudioPtr2, dwAudioBytes2);
    }
    // doesn't seem ever necessary, but fill the rest of the requested buffer with silence
    // if DirectSoundGenerator doesn't have enough
    if (size > dwAudioBytes1 + dwAudioBytes2)
    {
      memset(data + dwAudioBytes1 + dwAudioBytes2, 0, size - (dwAudioBytes1 + dwAudioBytes2));
    }
    
    dsg->setVolumeIfNecessary();
    
    return noErr;
  }
#endif // USE_COREAUDIO

}

void registerSoundBuffer(IDirectSoundBuffer * buffer)
{
  const std::shared_ptr<DirectSoundGenerator> generator = std::make_shared<DirectSoundGenerator>(buffer);
  activeSoundGenerators[buffer] = generator;
}

void unregisterSoundBuffer(IDirectSoundBuffer * buffer)
{
  const auto it = activeSoundGenerators.find(buffer);
  if (it != activeSoundGenerators.end())
  {
    // stop the QAudioOutput before removing. is this necessary?
    it->second->stop();
    activeSoundGenerators.erase(it);
  }
}

namespace sa2
{

  void stopAudio()
  {
    for (auto & it : activeSoundGenerators)
    {
      const std::shared_ptr<DirectSoundGenerator> & generator = it.second;
      generator->stop();
    }
  }

  void writeAudio(const char * deviceName, const size_t ms)
  {
    for (auto & it : activeSoundGenerators)
    {
      const std::shared_ptr<DirectSoundGenerator> & generator = it.second;
      generator->writeAudio(deviceName, ms);
    }
  }

  void printAudioInfo()
  {
    for (auto & it : activeSoundGenerators)
    {
      const std::shared_ptr<DirectSoundGenerator> & generator = it.second;
      generator->printInfo();
    }
  }

  void resetUnderruns()
  {
    for (auto & it : activeSoundGenerators)
    {
      const std::shared_ptr<DirectSoundGenerator> & generator = it.second;
      generator->resetUnderruns();
    }
  }

  std::vector<SoundInfo> getAudioInfo()
  {
    std::vector<SoundInfo> info;
    info.reserve(activeSoundGenerators.size());

    for (auto & it : activeSoundGenerators)
    {
      const std::shared_ptr<DirectSoundGenerator> & generator = it.second;
      info.push_back(generator->getInfo());
    }

    return info;
  }

}
