// File
// ====

function file_size(file) {
  const fs = require("fs");
  const win = process.platform === "win32";
  try {
    const size = fs.fstatSync(file).size;
    if (win) {
      return io_tup(file, size > 4294967295
        ? io_fail(require("os").constants.errno.EOVERFLOW) : io_done(size));
    }
    const over = io_sys().mac ? 84 : 75;
    return io_tup(file, size > 4294967295 ? io_fail(over) : io_done(size));
  } catch (e) {
    if (win) {
      return io_tup(file, io_fail(io_code(e)));
    }
    return io_tup(file, io_fail(Math.abs(e.errno ?? 5)));
  }
}

io_eff(CID(File.size), file_size);
