// The fork's parity gate: on Linux and macOS this checkout compiles every
// program as main does. Both compilers emit each program under the dirs
// named (tests/io, tests/gfx, tests/run, bench/runtime and demos by
// default), each from its own base and effects. Each lane's C (the CPU's,
// CUDA's host and device, Metal's host and device) is preprocessed as that
// lane's compiler would, with empty system headers, and the two must match
// line for line: what those compilers see is main's. The JS lane differs only
// by its win32 arms; their distinct hunks print, for a reader to check.
// $PARITY_MAIN names main (a git ref), $CC the clang.

import * as child from "node:child_process";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import * as url from "node:url";

import * as Bend from "../bend2/bend.ts";
import * as Comp from "../bend2/comp.ts";

const ROOT = path.join(import.meta.dirname, "..");

const MAIN = process.env.PARITY_MAIN ?? "main";

const CC = process.env.CC ?? (process.platform === "win32"
  ? path.join(process.env.ProgramFiles ?? "C:\\Program Files", "LLVM", "bin",
    "clang.exe") : "clang");

const DIRS = ["tests/io", "tests/gfx", "tests/run", "bench/runtime", "demos"];

// The lanes, as their compilers see the source: the flags main.ts builds
// with, NVRTC's (gpu_make) and Metal's (a C++ dialect).
const LANES: [string, string[]][] = [
  ["linux", ["--target=x86_64-linux-gnu", "-x", "c"]],
  ["linux-cuda", ["--target=x86_64-linux-gnu", "-x", "c", "-DBEND_CUDA=1"]],
  ["cuda-dev", ["--target=x86_64-linux-gnu", "-x", "c", "-D__CUDACC_RTC__=1",
    "-D__CUDACC__=1", "-DCUBE_LOG=7"]],
  ["ptx-dev", ["--target=nvptx64-nvidia-cuda", "-x", "c", "-D__CUDACC_RTC__=1",
    "-D__CUDACC__=1", "-DCUBE_LOG=7"]],
  ["mac", ["--target=arm64-apple-macos14", "-x", "c"]],
  ["mac-metal", ["--target=arm64-apple-macos14", "-x", "objective-c",
    "-DBEND_METAL=1"]],
  ["metal-dev", ["--target=arm64-apple-macos14", "-x", "c++",
    "-D__METAL_VERSION__=320"]],
  ["metal-dev-310", ["--target=arm64-apple-macos14", "-x", "c++",
    "-D__METAL_VERSION__=310"]],
];

type Lane = { comp: typeof Comp, dir: string };

// main's bend2, from git, under tmp
async function main_lane(tmp: string): Promise<Lane> {
  const tar = child.spawnSync("git", ["archive", "--format=tar", MAIN, "bend2"],
    { cwd: ROOT, maxBuffer: 1 << 28 });
  if (tar.status !== 0
    || child.spawnSync("tar", ["-xf", "-"], { cwd: tmp, input: tar.stdout })
      .status !== 0) {
    throw new Error("cannot extract " + MAIN + "'s bend2");
  }
  const at = (f: string): string => url.pathToFileURL(path.join(tmp, "bend2", f))
    .href;
  return { comp: await import(at("comp.ts")), dir: path.join(tmp, "bend2") };
}

// A book loaded by this checkout's loader; main's reads main's effects, as
// its foreign defs import them from its bend2.
async function book_of(file: string, from?: string): Promise<Bend.Book | null> {
  const book = Bend.book_nil();
  try {
    await Bend.book_load(book, file.replaceAll(path.sep, "/"), "", new Map());
    Bend.book_valid(book, 0);
  } catch {
    return null;
  }
  const ours = path.join(ROOT, "bend2").replaceAll(path.sep, "/") + "/";
  for (const tld of Object.values(book.tlds)) {
    if (from !== undefined && tld.$ === "Def" && tld.i !== undefined) {
      tld.i = tld.i.map((f) => f.startsWith(ours)
        ? from.replaceAll(path.sep, "/") + "/" + f.slice(ours.length) : f);
    }
  }
  return book;
}

function emit(f: () => string): string {
  try {
    return f();
  } catch (e) {
    return "// threw: " + String(e instanceof Error ? e.message : e);
  }
}

// A header any source includes is empty under stubs.
function stubs_add(stubs: string, src: string): void {
  for (const m of src.matchAll(/^\s*#\s*(?:include|import)\s*[<"]([^>"]+)[>"]/gm)) {
    const f = path.join(stubs, m[1]);
    if (!fs.existsSync(f)) {
      fs.mkdirSync(path.dirname(f), { recursive: true });
      fs.writeFileSync(f, "");
    }
  }
}

// #embed __FILE__ carries the whole source to the device: what the device
// compiles is checked as its own lane.
function pre(src: string, flags: string[], stubs: string): Promise<string> {
  const text = src.replace(/^#embed __FILE__.*$/gm, "/* embed */");
  return new Promise((done) => {
    const p = child.spawn(CC, ["-E", "-P", "-nostdinc", "-isystem", stubs,
      "-iquote", stubs, ...flags, "-"]);
    const out: Buffer[] = [];
    const err: Buffer[] = [];
    p.stdout.on("data", (b) => out.push(b));
    p.stderr.on("data", (b) => err.push(b));
    p.on("close", (code) => done(code === 0
      ? Buffer.concat(out).toString().split("\n").map((l) => l.trimEnd())
        .filter((l) => l !== "").join("\n")
      : "// failed: " + Buffer.concat(err).toString().split("\n")
        .filter((l) => / error: /.test(l)).map((l) => l.replace(/^.*?error: /,
          "")).join("\n")));
    p.stdin.end(text);
  });
}

// at most n at a time
async function pool<T>(jobs: (() => Promise<T>)[], n: number): Promise<T[]> {
  const got: T[] = new Array(jobs.length);
  let next = 0;
  await Promise.all(Array.from({ length: n }, async () => {
    while (next < jobs.length) {
      const i = next++;
      got[i] = await jobs[i]();
    }
  }));
  return got;
}

function diff(tmp: string, a: string, b: string): string {
  fs.writeFileSync(path.join(tmp, "a"), a);
  fs.writeFileSync(path.join(tmp, "b"), b);
  return child.spawnSync("git", ["diff", "--no-index", "-U0", "--no-color",
    path.join(tmp, "a"), path.join(tmp, "b")], { maxBuffer: 1 << 28 }).stdout
    .toString();
}

if (import.meta.main) {
  const dirs = process.argv.slice(2).length > 0 ? process.argv.slice(2) : DIRS;
  const files = dirs.flatMap(function walk(d: string): string[] {
    const at = path.join(ROOT, d);
    return fs.statSync(at).isFile() ? [at] : fs.readdirSync(at).sort()
      .flatMap((f) => f.endsWith(".bend") ? [path.join(at, f)]
        : fs.statSync(path.join(at, f)).isDirectory() ? walk(path.join(d, f))
        : []);
  });
  const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "bend-parity-"));
  const stubs = path.join(tmp, "stubs");
  const main = await main_lane(tmp);
  const hunks = new Map<string, string[]>();
  // the programs compared, those this checkout cannot load or emit (both
  // refuse alike, or it fails), and lanes neither preprocesses (the same error)
  let checked = 0;
  let fails = 0;
  let refused = 0;
  let broken = 0;
  try {
    for (const file of files) {
      const name = path.relative(ROOT, file).replaceAll(path.sep, "/");
      const ours = await book_of(file);
      const theirs = await book_of(file, main.dir);
      if (ours === null || theirs === null) {
        refused += 1;
        console.log("unloaded " + name);
        continue;
      }
      const c = [emit(() => main.comp.compile_book(theirs)),
        emit(() => Comp.compile_book(ours))];
      if (c[1].startsWith("// threw")) {
        refused += 1;
        fails += c[0] !== c[1] ? 1 : 0;
        console.log((c[0] !== c[1] ? "FAIL " : "refused ") + name + ": " + c[1]);
        continue;
      }
      const js = [emit(() => main.comp.js_book(theirs)),
        emit(() => Comp.js_book(ours))];
      stubs_add(stubs, c[0] + c[1]);
      const outs = await pool(LANES.flatMap(([, flags]) =>
        c.map((src) => () => pre(src, flags, stubs))), 4);
      checked += 1;
      for (const [i, [lane]] of LANES.entries()) {
        broken += outs[2 * i + 1].startsWith("// failed") ? 1 : 0;
        if (outs[2 * i] !== outs[2 * i + 1]) {
          fails += 1;
          console.log("FAIL " + name + " (" + lane + ")\n"
            + diff(tmp, outs[2 * i], outs[2 * i + 1]).split("\n").slice(4, 40)
              .join("\n"));
        }
      }
      for (const h of diff(tmp, js[0], js[1]).split(/^@@.*$/m).slice(1)) {
        hunks.set(h, [...(hunks.get(h) ?? []), name]);
      }
    }
  } finally {
    fs.rmSync(tmp, { recursive: true, force: true });
  }
  for (const [h, names] of hunks) {
    console.log("JS hunk, in " + String(names.length) + " (" + names[0] + "):"
      + h.trimEnd());
  }
  console.log((fails === 0 ? "PASS" : "FAIL") + ": " + String(checked)
    + " programs in " + String(LANES.length) + " C lanes, " + String(fails)
    + " mismatched, " + String(refused) + " not loaded or emitted, "
    + String(broken) + " lanes not preprocessed; " + String(hunks.size)
    + " distinct JS hunks");
  process.exitCode = fails === 0 ? 0 : 1;
}
