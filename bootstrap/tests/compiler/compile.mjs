// Runs Compiler.compile on the bytes of a book with the JS that `bend -o` writes
// for compile.bend: a fast run of our compiler, for the tests, by a runtime
// that we do not trust (run.sh checks it against the Lean interpreter when
// TRUSTED is set). That JS recurses on lists, so it runs in a worker with a
// large stack.
//
//   node compile.mjs <compile.mjs of bend -o> <book> <module.wasm>
import { readFileSync, writeFileSync } from "node:fs";
import { isMainThread, Worker } from "node:worker_threads";
import { pathToFileURL } from "node:url";

const [js, book, out] = process.argv.slice(2);
if (isMainThread) {
  const worker = new Worker(new URL(import.meta.url), {
    argv: [js, book, out],
    resourceLimits: { stackSizeMb: 2000, maxOldGenerationSizeMb: 16000 },
  });
  worker.on("error", (e) => {
    console.error(e);
    process.exit(1);
  });
  worker.on("exit", (code) => process.exit(code));
} else {
  const { default: m } = await import(pathToFileURL(js).href);
  const bytes = readFileSync(book);
  let list = { $: "Nil" };
  for (let k = bytes.length - 1; k >= 0; k--) list = { $: "Con", head: bytes[k], tail: list };
  const wasm = [];
  for (let r = m.main(list); r.$ === "Con"; r = r.tail) wasm.push(r.head);
  writeFileSync(out, Uint8Array.from(wasm));
}
