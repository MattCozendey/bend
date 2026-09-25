// Window
// ======

#ifdef __OBJC__

#import <AppKit/AppKit.h>

static void window_close(intptr_t at) {
  NSWindow* win = CFBridgingRelease((void*)at);
  [win close];
}

#elif defined(__linux__)

#ifndef BendWin
#define BendWin BendWin
#include <X11/Xlib.h>
#include <X11/Xutil.h>
#include <X11/keysym.h>

typedef struct {
  Display* dpy;
  Window   win;
  Atom     del;
  XImage*  img;
  u32      n;
  u32      cap;
  u32*     evs;
} BendWin;
#endif

static void window_close(intptr_t at) {
  BendWin* win = (BendWin*)at;
  XDestroyImage(win->img);
  XCloseDisplay(win->dpy);
  free(win->evs);
  free(win);
}

#elif defined(_WIN32)

// The Win32 window: a fixed client area, its frame's pixels (a top-down
// 32-bit DIB, 0x00RRGGBB as X11's image) and the events pumped since the
// last frame, five words each as on the Mac. The same block sits in each
// window file's Win32 lane under this guard.
#ifndef BendWin
#define BendWin BendWin
#pragma comment(lib, "user32")
#pragma comment(lib, "gdi32")

typedef struct {
  HWND       hwnd;
  BITMAPINFO bmi;
  u32*       pix;
  u32        w;
  u32        h;
  u32        n;
  u32        cap;
  u32*       evs;
} BendWin;
#endif

static void window_close(intptr_t at) {
  BendWin* win = (BendWin*)at;
  SetWindowLongPtrA(win->hwnd, GWLP_USERDATA, 0);
  DestroyWindow(win->hwnd);
  free(win->pix);
  free(win->evs);
  free(win);
}

#else

static void window_close(intptr_t at) {
}

#endif

Term window_close_run(Env e, Term* f, IoWork* w) {
  window_close((intptr_t)io_hand_v(f[0]));
  return term_pak(CID(Unit), 0);
}

static void __attribute__((constructor)) window_close_use(void) {
  io_eff(CID(Window.close), window_close_run, 0);
}
