// Audio
// =====

// The ring: 4096 float32 stereo frames. The effects fill it on the
// evaluator's thread; the device's callback drains it and pads the
// rest of its buffer with silence. All audio effects share this source;
// each entry is present only when its effect is reachable.
#ifndef IO_RING
#define IO_RING 4096u

#ifdef __OBJC__
#import <AudioToolbox/AudioToolbox.h>
#elif defined(__linux__)
#include <alsa/asoundlib.h>
#elif defined(_WIN32)
// the runtime's FAR is not the empty one Windows' headers expect
#pragma push_macro("FAR")
#undef FAR
#define FAR
#include <mmdeviceapi.h>
#include <audioclient.h>
#pragma pop_macro("FAR")
#pragma comment(lib, "ole32")
#endif

typedef struct {
  _Atomic(u64) read, written;
  float        pcm[IO_RING * 2];
#ifdef __OBJC__
  AudioUnit    unit;
#elif defined(__linux__)
  snd_pcm_t*   unit;
  pthread_t    pump;
  _Atomic(u32) done;
#elif defined(_WIN32)
  IAudioClient*       unit;
  IAudioRenderClient* feed;
  HANDLE              tick;
  UINT32              frames;
  pthread_t           pump;
  _Atomic(u32)        done;
#endif
} IoRing;

// n frames queued after the write; a write past the ring's room is
// dropped and the queue answered as it is.
static u64 io_ring_write(IoRing* p, const float* pcm, u32 n) {
  u64 w = atomic_load_explicit(&p->written, memory_order_relaxed);
  u64 r = atomic_load_explicit(&p->read, memory_order_acquire);
  if (w - r + n <= IO_RING) {
    u32 at    = (u32)(w % IO_RING);
    u32 first = n < IO_RING - at ? n : IO_RING - at;
    memcpy(p->pcm + at * 2, pcm, first * 8);
    memcpy(p->pcm, pcm + first * 2, (n - first) * 8);
    atomic_store_explicit(&p->written, w + n, memory_order_release);
    w += n;
  }
  return w - r;
}

static void io_ring_pull(IoRing* p, float* out, u32 frames) {
  u64 r     = atomic_load_explicit(&p->read, memory_order_relaxed);
  u64 w     = atomic_load_explicit(&p->written, memory_order_acquire);
  u32 n     = (u32)(w - r < frames ? w - r : frames);
  u32 at    = (u32)(r % IO_RING);
  u32 first = n < IO_RING - at ? n : IO_RING - at;
  memcpy(out, p->pcm + at * 2, first * 8);
  memcpy(out + first * 2, p->pcm, (n - first) * 8);
  memset(out + n * 2, 0, (frames - n) * 8);
  atomic_store_explicit(&p->read, r + n, memory_order_release);
}

#ifdef __OBJC__

static OSStatus io_ring_pump(void* ctx, AudioUnitRenderActionFlags* flags,
  const AudioTimeStamp* when, UInt32 bus, UInt32 frames,
  AudioBufferList* bl) {
  if (bl->mNumberBuffers != 1 || bl->mBuffers[0].mNumberChannels != 2
      || bl->mBuffers[0].mDataByteSize < frames * 8) {
    return kAudio_ParamError;
  }
  io_ring_pull(ctx, bl->mBuffers[0].mData, frames);
  return noErr;
}

// The default output unit fed float32 stereo at the asked rate (the
// unit converts to the device's own).
static u32 io_ring_start(IoRing* p, u32 rate) {
  AudioComponentDescription desc = { kAudioUnitType_Output,
    kAudioUnitSubType_DefaultOutput, kAudioUnitManufacturer_Apple, 0, 0 };
  AudioComponent comp = AudioComponentFindNext(NULL, &desc);
  if (comp == NULL || AudioComponentInstanceNew(comp, &p->unit) != noErr) {
    return ENODEV;
  }
  AudioStreamBasicDescription fmt = { 0 };
  fmt.mSampleRate       = rate;
  fmt.mFormatID         = kAudioFormatLinearPCM;
  fmt.mFormatFlags      = kAudioFormatFlagIsFloat | kAudioFormatFlagIsPacked;
  fmt.mBytesPerPacket   = 8;
  fmt.mFramesPerPacket  = 1;
  fmt.mBytesPerFrame    = 8;
  fmt.mChannelsPerFrame = 2;
  fmt.mBitsPerChannel   = 32;
  AURenderCallbackStruct cb = { io_ring_pump, p };
  bool ok = AudioUnitSetProperty(p->unit, kAudioUnitProperty_StreamFormat,
      kAudioUnitScope_Input, 0, &fmt, sizeof fmt) == noErr
    && AudioUnitSetProperty(p->unit, kAudioUnitProperty_SetRenderCallback,
      kAudioUnitScope_Input, 0, &cb, sizeof cb) == noErr
    && AudioUnitInitialize(p->unit) == noErr
    && AudioOutputUnitStart(p->unit) == noErr;
  return ok ? 0 : ENODEV;
}

static void io_ring_free(IoRing* p) {
  if (p->unit != NULL) {
    AudioOutputUnitStop(p->unit);
    AudioUnitUninitialize(p->unit);
    AudioComponentInstanceDispose(p->unit);
  }
  free(p);
}

#elif defined(__linux__)

// A thread feeds the default ALSA device 256 frames at a time (a
// write blocks until the device has room, so the ring drains at the
// device's clock).
static void* io_ring_pump(void* ctx) {
  IoRing* p = ctx;
  float   out[256 * 2];
  while (atomic_load_explicit(&p->done, memory_order_relaxed) == 0) {
    io_ring_pull(p, out, 256);
    snd_pcm_sframes_t n = snd_pcm_writei(p->unit, out, 256);
    if (n < 0) {
      snd_pcm_recover(p->unit, (int)n, 1);
    }
  }
  return NULL;
}

static void io_ring_hush(const char* file, int line, const char* fn, int err,
  const char* fmt, ...) {
}

static u32 io_ring_start(IoRing* p, u32 rate) {
  snd_lib_error_set_handler(io_ring_hush);
  if (snd_pcm_open(&p->unit, "default", SND_PCM_STREAM_PLAYBACK, 0) < 0) {
    return ENODEV;
  }
  if (snd_pcm_set_params(p->unit, SND_PCM_FORMAT_FLOAT_LE,
    SND_PCM_ACCESS_RW_INTERLEAVED, 2, rate, 1, 20000) < 0
    || pthread_create(&p->pump, NULL, io_ring_pump, p) != 0) {
    return ENODEV;
  }
  return 0;
}

static void io_ring_free(IoRing* p) {
  if (p->unit != NULL) {
    atomic_store_explicit(&p->done, 1, memory_order_relaxed);
    if (p->pump != 0) {
      pthread_join(p->pump, NULL);
    }
    snd_pcm_close(p->unit);
  }
  free(p);
}

#elif defined(_WIN32)

static const GUID io_ring_enum_cls = { 0xBCDE0395, 0xE52F, 0x467C,
  { 0x8E, 0x3D, 0xC4, 0x57, 0x92, 0x91, 0x69, 0x2E } };
static const GUID io_ring_enum_iid = { 0xA95664D2, 0x9614, 0x4F35,
  { 0xA7, 0x46, 0xDE, 0x8D, 0xB6, 0x36, 0x17, 0xE6 } };
static const GUID io_ring_unit_iid = { 0x1CB9AD4C, 0xDBFA, 0x4C32,
  { 0xB1, 0x78, 0xC2, 0xF5, 0x68, 0xA7, 0x03, 0xB2 } };
static const GUID io_ring_feed_iid = { 0xF294ACFC, 0x3146, 0x4483,
  { 0xA7, 0xBF, 0xAD, 0xDC, 0xA7, 0xC2, 0x60, 0xE2 } };

// A thread refills the WASAPI buffer each time the device signals room,
// so the ring drains at the device's clock, as ALSA's. It moves only the
// frames the ring holds: the device's buffer covers a late write, and a
// block of silence would be heard.
static void* io_ring_pump(void* ctx) {
  IoRing* p = ctx;
  CoInitializeEx(NULL, COINIT_MULTITHREADED);
  while (atomic_load_explicit(&p->done, memory_order_relaxed) == 0) {
    UINT32 used = p->frames;
    BYTE*  out  = NULL;
    WaitForSingleObject(p->tick, 100);
    p->unit->lpVtbl->GetCurrentPadding(p->unit, &used);
    u64    held = atomic_load_explicit(&p->written, memory_order_acquire)
      - atomic_load_explicit(&p->read, memory_order_relaxed);
    UINT32 n    = p->frames - used < held ? p->frames - used : (UINT32)held;
    if (n > 0 && SUCCEEDED(p->feed->lpVtbl->GetBuffer(p->feed, n, &out))) {
      io_ring_pull(p, (float*)out, n);
      p->feed->lpVtbl->ReleaseBuffer(p->feed, n, 0);
    }
  }
  CoUninitialize();
  return NULL;
}

// The default device in shared mode, fed float32 stereo at the asked rate
// (Windows converts to the device's own), a 20 ms buffer as ALSA's.
static bool io_ring_unit(IoRing* p, u32 rate) {
  IMMDeviceEnumerator* en  = NULL;
  IMMDevice*           dev = NULL;
  WAVEFORMATEX         fmt = { WAVE_FORMAT_IEEE_FLOAT, 2, rate, rate * 8, 8,
    32, 0 };
  CoInitializeEx(NULL, COINIT_MULTITHREADED);
  bool ok = SUCCEEDED(CoCreateInstance(&io_ring_enum_cls, NULL, CLSCTX_ALL,
      &io_ring_enum_iid, (void**)&en))
    && SUCCEEDED(en->lpVtbl->GetDefaultAudioEndpoint(en, eRender, eConsole,
      &dev))
    && SUCCEEDED(dev->lpVtbl->Activate(dev, &io_ring_unit_iid, CLSCTX_ALL,
      NULL, (void**)&p->unit))
    && SUCCEEDED(p->unit->lpVtbl->Initialize(p->unit, AUDCLNT_SHAREMODE_SHARED,
      AUDCLNT_STREAMFLAGS_EVENTCALLBACK | AUDCLNT_STREAMFLAGS_AUTOCONVERTPCM
      | AUDCLNT_STREAMFLAGS_SRC_DEFAULT_QUALITY, 200000, 0, &fmt, NULL));
  if (dev != NULL) {
    dev->lpVtbl->Release(dev);
  }
  if (en != NULL) {
    en->lpVtbl->Release(en);
  }
  return ok;
}

static u32 io_ring_start(IoRing* p, u32 rate) {
  bool ok = io_ring_unit(p, rate)
    && (p->tick = CreateEventA(NULL, FALSE, FALSE, NULL)) != NULL
    && SUCCEEDED(p->unit->lpVtbl->SetEventHandle(p->unit, p->tick))
    && SUCCEEDED(p->unit->lpVtbl->GetBufferSize(p->unit, &p->frames))
    && SUCCEEDED(p->unit->lpVtbl->GetService(p->unit, &io_ring_feed_iid,
      (void**)&p->feed))
    && SUCCEEDED(p->unit->lpVtbl->Start(p->unit))
    && pthread_create(&p->pump, NULL, io_ring_pump, p) == 0;
  return ok ? 0 : ENODEV;
}

static void io_ring_free(IoRing* p) {
  if (p->pump != NULL) {
    atomic_store_explicit(&p->done, 1, memory_order_relaxed);
    pthread_join(p->pump, NULL);
  }
  if (p->feed != NULL) {
    p->feed->lpVtbl->Release(p->feed);
  }
  if (p->unit != NULL) {
    p->unit->lpVtbl->Stop(p->unit);
    p->unit->lpVtbl->Release(p->unit);
  }
  if (p->tick != NULL) {
    CloseHandle(p->tick);
  }
  free(p);
}

#else

static u32 io_ring_start(IoRing* p, u32 rate) {
  return ENOTSUP;
}

static void io_ring_free(IoRing* p) {
  free(p);
}

#endif
#endif

#ifdef CID(Audio.open)
Term audio_open_run(Env e, Term* f, IoWork* w) {
  u32     rate = (u32)f[0];
  IoRing* p    = io_mem(calloc(1, sizeof *p));
  u32     code = rate < 8000 || rate > 192000 ? EINVAL : io_ring_start(p, rate);
  if (code != 0) {
    io_ring_free(p);
    return io_fail(e, code, code == EINVAL ? NULL : "Audio.open: no audio output");
  }
  return io_done(e, io_hand((intptr_t)p));
}

static void __attribute__((constructor)) audio_open_use(void) {
  io_eff(CID(Audio.open), audio_open_run, 0);
}
#endif

#ifdef CID(Audio.write)
// The samples (interleaved L R ...) into the ring; the frames queued
// after the write. Past the ring's room, the samples are dropped and
// the queue answered as it is.
Term audio_write_run(Env e, Term* f, IoWork* w) {
  IoRing* p   = (IoRing*)(uintptr_t)io_hand_v(f[0]);
  float   pcm[IO_RING * 2];
  u32     n   = 0;
  Term    s   = f[1];
  while (term_aux(s) == CID(Con)) {
    Term fb[2];
    spare_free(e, cls_fit(2), ctr_take(e, s, 2, fb));
    if (n < IO_RING * 2) {
      pcm[n] = f32_unbox(fb[0]);
    }
    n += 1;
    s  = fb[1];
  }
  u64 q = n > IO_RING * 2 ? io_ring_write(p, pcm, 0)
    : io_ring_write(p, pcm, n / 2);
  return io_tup(e, f[0], q);
}

static void __attribute__((constructor)) audio_write_use(void) {
  io_eff(CID(Audio.write), audio_write_run, 0);
}
#endif

#ifdef CID(Audio.close)
Term audio_close_run(Env e, Term* f, IoWork* w) {
  io_ring_free((IoRing*)(uintptr_t)io_hand_v(f[0]));
  return term_pak(CID(Unit), 0);
}

static void __attribute__((constructor)) audio_close_use(void) {
  io_eff(CID(Audio.close), audio_close_run, 0);
}
#endif
