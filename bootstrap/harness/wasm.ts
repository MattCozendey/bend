#!/usr/bin/env bun
// Runs a module that the compiler in Bend wrote, by the protocol of
// bend/src/wasm/impl.bend, on the engine of bun (JavaScriptCore) or node (V8).
//
//   bun wasm.ts <file.wasm> [input-file] [pages]
//   node wasm.ts <file.wasm> [input-file] [pages]
//
// - The module gets a memory of `pages` pages (1 to 65535, by default 256).
// - The input's length (4 bytes, the low byte first) goes at 0, its bytes at 4.
// - main returns an address p. The output is the length at p and the bytes
//   after it; they go to stdout.
// - A failure exits 1 with a message that names its kind: "trap" (the run
//   trapped), "invalid module", "link error", or "error" (the input or output
//   does not fit).

// Imports
// =======

import * as fs from "node:fs";

// Constants
// =========

const DEFAULT_PAGES = 256;

const USAGE = "usage: wasm.ts <file.wasm> [input-file] [pages]";

// Functions
// =========

// getKind e: the kind of the failure e
const getKind = (e: unknown): string =>
  e instanceof WebAssembly.RuntimeError ? "trap"
    : e instanceof WebAssembly.CompileError ? "invalid module"
    : e instanceof WebAssembly.LinkError ? "link error"
    : "error";

// getOutput wasm input pages: the output bytes of the module wasm for input
const getOutput = (wasm: Uint8Array, input: Uint8Array, pages: number): Uint8Array => {
  const memory = new WebAssembly.Memory({ initial: pages });
  const size = memory.buffer.byteLength;
  if (4 + input.length > size) {
    throw new Error("the input does not fit");
  }
  const view = new DataView(memory.buffer);
  view.setUint32(0, input.length, true);
  new Uint8Array(memory.buffer).set(input, 4);
  const instance = new WebAssembly.Instance(new WebAssembly.Module(wasm), { env: { memory } });
  const p = (instance.exports["main"] as () => number)() >>> 0;
  if (p + 4 > size) {
    throw new Error("the output's length is out of bounds");
  }
  const n = view.getUint32(p, true);
  if (p + 4 + n > size) {
    throw new Error("the output is out of bounds");
  }
  return new Uint8Array(memory.buffer, p + 4, n);
};

// Side effects
// ============

const [file, inputFile, pagesText] = process.argv.slice(2);
const pages = pagesText === undefined ? DEFAULT_PAGES : Number(pagesText);
if (file === undefined || !Number.isInteger(pages) || pages < 1 || pages > 65535) {
  console.error(USAGE);
  process.exit(2);
}
try {
  const input = inputFile === undefined ? new Uint8Array(0) : new Uint8Array(fs.readFileSync(inputFile));
  process.stdout.write(getOutput(new Uint8Array(fs.readFileSync(file)), input, pages));
} catch (e) {
  console.error(`${getKind(e)}: ${e instanceof Error ? e.message : String(e)}`);
  process.exit(1);
}
