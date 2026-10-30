#!/usr/bin/env bun
// Writes cases/wasm.json and cases/wasm_engines.json, the cases of the
// modules of cases/wasm.bend:
//
//   bun gen_wasm.ts <i32.wast>
//
// - The vectors of the i32 operations, and their results, come from i32.wast
//   of the official WebAssembly testsuite (github.com/WebAssembly/testsuite),
//   at commit 63908677d00585fdab4c4eccbf01f781d3a454d5.
// - wasm.json runs each module by the meaning (mode 0, and mode 2 for no
//   input): it expects 1 and the output, or 0 at a trap.
// - wasm_engines.json gives each module as binary (mode 1), for an engine
//   with 1 page (harness/wasm.ts): it expects the output, or a trap. Run it
//   with one --run for each engine (see PLAN.md, Tests).

// Imports
// =======

import * as fs from "node:fs";
import * as path from "node:path";

// Types
// =====

// a test of cases/wasm.bend: its number, its data, and its output (none at a
// trap)
type Test = { name: string; test: number; data: number[]; out: number[] | undefined };

type Expect = { hex: string } | { refused: string };

type Case = { name: string; program: string; input: string; expect: Expect };

// Constants
// =========

// the operations of tests 0 to 11, in the order of cases/wasm.bend
const OPS = ["add", "sub", "and", "or", "xor", "shl", "shr_u", "eq", "ne", "lt_u", "ge_u", "eqz"];

const ASSERT = /\(assert_return \(invoke "(\w+)"((?: \(i32\.const [^)]+\))+)\) \(i32\.const ([^)]+)\)\)/g;

const CASES = path.join(import.meta.dirname, "cases");

// tests 12 to 20 of cases/wasm.bend
const OTHERS: Test[] = [
  { name: "a loop sums the input's bytes", test: 12, data: [65, 66, 67], out: [198, 0, 0, 0] },
  { name: "a loop sums no bytes", test: 12, data: [], out: [0, 0, 0, 0] },
  { name: "br_table takes label 0", test: 13, data: [0], out: [10, 0, 0, 0] },
  { name: "br_table takes label 1", test: 13, data: [1], out: [11, 0, 0, 0] },
  { name: "br_table takes label 2", test: 13, data: [2], out: [12, 0, 0, 0] },
  { name: "br_table takes its default", test: 13, data: [7], out: [99, 0, 0, 0] },
  { name: "stores and loads of i32s and bytes, tee and drop", test: 14, data: [],
    out: [0x33, 0x33, 0x22, 0x11, 0xff, 0x01] },
  { name: "a load that ends past the memory traps", test: 15, data: [], out: undefined },
  { name: "a load whose address passes 2^32 traps", test: 16, data: [], out: undefined },
  { name: "a load that ends at the end of the memory does not trap", test: 17, data: [], out: [] },
  { name: "unreachable traps", test: 18, data: [], out: undefined },
  { name: "the length of no bytes is at 0", test: 19, data: [], out: [0, 0, 0, 0] },
  { name: "the input's length is at 0", test: 19, data: [7, 8, 9], out: [3, 0, 0, 0] },
  { name: "memory.size gives the number of pages", test: 20, data: [], out: [1, 0, 0, 0] },
];

// test 19 with no input (mode 2), by the meaning only: each engine case has an
// input
const NO_INPUT: Test = { name: "0xffffffff is at 0 for no input", test: 19, data: [], out: [255, 255, 255, 255] };

// Functions
// =========

// getBytes v: the 4 bytes of the i32 v, the low byte first
const getBytes = (v: bigint): number[] => [0n, 8n, 16n, 24n].map((s) => Number((v >> s) & 0xffn));

// getI32 text: the i32 that a constant of i32.wast shows
const getI32 = (text: string): bigint => BigInt.asUintN(32, BigInt(text.replaceAll("_", "")));

// getOpTests wast: tests 0 to 11, with the vectors of each operation
const getOpTests = (wast: string): Test[] => {
  const asserts = [...wast.matchAll(ASSERT)].filter((m) => OPS.includes(m[1] as string));
  return OPS.map((op, test) => {
    const mine = asserts.filter((m) => m[1] === op);
    const args = mine.map((m) => [...(m[2] as string).matchAll(/i32\.const ([^)]+)/g)].map((a) => getI32(a[1] as string)));
    return {
      name: `i32.${op} gives the results of i32.wast (${mine.length} vectors)`,
      test,
      data: args.flatMap(([a, b]) => [...getBytes(a ?? 0n), ...getBytes(b ?? 0n)]),
      out: mine.flatMap((m) => getBytes(getI32(m[3] as string))),
    };
  });
};

// getHex bytes: bytes in hex
const getHex = (bytes: number[]): string => Buffer.from(bytes).toString("hex");

// getCase t mode: the case of the test t, run by an engine (mode 1) or the
// meaning (another mode)
const getCase = (t: Test, mode: number): Case => ({
  name: t.name,
  program: "wasm.bend",
  input: getHex([mode, t.test, ...t.data]),
  expect: mode === 1
    ? t.out === undefined ? { refused: "trap" } : { hex: getHex(t.out) }
    : { hex: t.out === undefined ? "00" : getHex([1, ...t.out]) },
});

// Side effects
// ============

const wast = process.argv[2];
if (wast === undefined) {
  console.error("usage: gen_wasm.ts <i32.wast>");
  process.exit(2);
}
const tests = [...getOpTests(fs.readFileSync(wast, "utf8")), ...OTHERS];
fs.writeFileSync(path.join(CASES, "wasm.json"),
  JSON.stringify([...tests.map((t) => getCase(t, 0)), getCase(NO_INPUT, 2)], null, 2) + "\n");
fs.writeFileSync(path.join(CASES, "wasm_engines.json"),
  JSON.stringify(tests.map((t) => getCase(t, 1)), null, 2) + "\n");
