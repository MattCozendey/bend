// File
// ====

function file_open(path, mode) {
  const name = io_bytes(path);
  if (name.includes(0)) {
    return io_fail({ darwin: 92, win32: 42 }[process.platform] ?? 84);
  }
  if (!["r", "w", "a"].includes(mode)) {
    return io_fail(22);
  }
  try {
    const fd = require("fs")
      .openSync(name.length > 0 ? Buffer.from(name) : "", mode, 0o644);
    return io_done(fd);
  } catch (e) {
    return io_fail(io_code(e));
  }
}

io_eff(CID(File.open), file_open);
