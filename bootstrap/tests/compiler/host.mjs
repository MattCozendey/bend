// The host of W5 in a real engine: runs a compiled module on the bytes of a
// file, and writes the bytes of its result to a file. It runs in bun
// (JavaScriptCore) and in node (V8).
//
//   bun host.mjs <module.wasm> <input> <output>
//
// Prints result, out_of_memory or no_result, and exits with 0 on a result.
import { readFileSync, writeFileSync } from "node:fs";

const [wasm, input, output] = process.argv.slice(2);
const data = readFileSync(input);
const { instance } = await WebAssembly.instantiate(readFileSync(wasm), {});
const { memory, alloc, run } = instance.exports;
const at = alloc(data.length) >>> 0;
if (at === 0xffffffff) {
  console.log("out_of_memory");
  process.exit(1);
}
new Uint8Array(memory.buffer).set(data, at);
const status = run(at, data.length) >>> 0;
if (status === 0) {
  const view = new DataView(memory.buffer);
  writeFileSync(output, new Uint8Array(memory.buffer, view.getUint32(0, true), view.getUint32(4, true)));
  console.log("result");
  process.exit(0);
}
console.log(status === 1 ? "out_of_memory" : status === 2 ? "no_result" : `status ${status}`);
process.exit(1);
