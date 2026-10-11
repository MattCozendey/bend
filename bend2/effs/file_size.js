// File
// ====

function file_size(file) {
  const fs = require("fs");
  try {
    const size = fs.fstatSync(file).size;
    // the EOVERFLOW errno, 84 on mac, 132 on Windows and 75 elsewhere.
    // io_sys().mac reads the same platform, but io_sys() binds libc through
    // bun:ffi, and on a host without it that ask threw where the size was
    // already read, so the catch answered Fail on a good file. Nothing above
    // this line touches the FFI table, and nothing below it should either.
    const over = { darwin: 84, win32: 132 }[process.platform] ?? 75;
    return io_tup(file, size > 4294967295 ? io_fail(over) : io_done(size));
  } catch (e) {
    return io_tup(file, io_fail(io_code(e)));
  }
}

io_eff(CID(File.size), file_size);
