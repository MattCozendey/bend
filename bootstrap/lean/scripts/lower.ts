// lower.ts
// ========
//
// Writes the BendTT lowering (bend2/safe.ts, as `bend -o` does) of a .bend
// file whose book bend2 checks but for its holes (?TODO): each hole is read as
// a call of its own def, so that the defs that name a hole stay in the output.
// Only the defs with a hole, and the proofs that call them, differ from what
// `bend -o` will write once the holes are filled; scripts/Defs.lean copies
// from it only defs and types that name no hole (src/Bootstrap/Copy/Trusted.lean).
//
//   cd bootstrap/bend/src/compiler && bun ../../../lean/scripts/lower.ts trusted.bend out.bendtt

import * as Bend from "../../../bend2/bend.ts";
import * as Safe from "../../../bend2/safe.ts";

const [file, out] = process.argv.slice(2);
const book = Bend.book_nil();
await Bend.book_load(book, file, "", new Map<string, string | null>());
Bend.book_valid(book, 0);
let holes = 0;
const fill = (x: any, self: string, seen: Set<any>): any => {
  if (x === null || typeof x !== "object" || seen.has(x)) return x;
  seen.add(x);
  if (x.$ === "Hol") {
    holes += 1;
    return { $: "Ref", k: self };
  }
  for (const k of Object.keys(x)) {
    if (k !== "s") x[k] = fill(x[k], self, seen);
  }
  return x;
};
for (const k in book.tlds) {
  const t: any = book.tlds[k];
  if (t.$ === "Def" && t.e) t.e = fill(t.e, k, new Set());
}
const oos = Safe.safe_emit(book, out);
console.log(`${holes} holes read as calls`);
if (oos.length !== 0) console.log("out of scope:\n" + oos.join(""));
