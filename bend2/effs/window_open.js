// Window
// ======

// ENOTSUP: Windows' is 129 (a page's bundle has no os module to ask)
function window_open(title, width, height) {
  const code = process.platform === "win32" ? 129
    : process.platform === "darwin" ? 45 : 95;
  const text = "Window.open: no display (build a native binary with bend <file> -o <out> and run it from a desktop session)";
  return { $: CID(Fail), error: { $: CID(Tuple), fst: code, snd: text } };
}

io_eff(CID(Window.open), window_open);
