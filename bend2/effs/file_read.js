// File
// ====

// Windows reads through Node's fs: the fd is the C runtime's, not an fd
// for read(2).
function file_read_win(file, max, offset, pack) {
  const len = Math.min(max, 2147483647);
  const b = new Uint8Array(Math.max(len, 1));
  try {
    const n = require("fs").readSync(file, b, 0, len, offset);
    return io_tup(file, io_done(pack(b, n)));
  } catch (e) {
    return io_tup(file, io_fail(io_code(e)));
  }
}

function file_read_with(file, max, offset, pack) {
  if (process.platform === "win32") {
    return file_read_win(file, max, offset, pack);
  }
  const sys = io_sys();
  const len = Math.min(max, 2147483647);
  const b = new Uint8Array(Math.max(len, 1));
  const n = Number(offset === null ? sys.read(file, sys.ptr(b), len)
    : sys.pread(file, sys.ptr(b), len, BigInt(offset)));
  return io_tup(file, n < 0 ? io_fail(sys.errno()) : io_done(pack(b, n)));
}

function file_read_list(b, n) {
  let xs = { $: CID(Nil) };
  for (let i = n; i > 0; i -= 1) {
    xs = { $: CID(Con), head: b[i - 1], tail: xs };
  }
  return xs;
}

function file_read(file, max) {
  return file_read_with(file, max, null, io_text);
}

function file_read_bytes(file, max) {
  return file_read_with(file, max, null, file_read_list);
}

function file_read_at(file, offset, max) {
  return file_read_with(file, max, offset, file_read_list);
}

io_eff(CID(File.read), file_read);
io_eff(CID(File.read_bytes), file_read_bytes);
io_eff(CID(File.read_at), file_read_at);
