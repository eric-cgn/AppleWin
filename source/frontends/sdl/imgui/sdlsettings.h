#pragma once

#include "frontends/sdl/imgui/gles.h"
#include "frontends/sdl/sdirectsound.h"

namespace sa2
{

  class SDLFrame;

  class ImGuiSettings
  {
  public:
    void show(SDLFrame* frame);
    float drawMenuBar();

    bool windowed = false;

  private:
    bool myShowDemo = false;
    bool myShowSettings = false;
    bool myShowMemory = false;
    bool myShowDebugger = false;
    bool mySyncCPU = true;
    bool myShowAbout = false;

    int myStepCycles = 0;
    int mySpeakerVolume;
    int myMockingboardVolume;

    MemoryEditor myMainMemoryEditor;
    MemoryEditor myAuxMemoryEditor;

    std::vector<SoundInfo> myAudioInfo;

    void showSettings(SDLFrame* frame);
    void showDebugger(SDLFrame* frame);
    void showMemory();
    void showAboutWindow();

    void drawDisassemblyTable();
    void drawConsole();
  };

}