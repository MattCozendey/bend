#!/usr/bin/env bun
// The bootstrap harness. It runs each case of a case list on each
// implementation that --run names, and checks the output.
//
//   bun harness.ts --run '<command>' [--run '<command>'] [--make '<command>']
//     [--work <dir>] <cases.json>
//
// - A command is words. Quotes join a word. It runs in the work directory,
//   so name its program by a full path.
// - --run is the implementation. {program} is the .bendtt file and {input}
//   is the input file. A word that names {input} goes when the case has no
//   input. The implementation writes the output bytes to stdout, and exits
//   non-zero to refuse.
// - --make turns a .bend program into .bendtt: {source} (its path from the
//   work directory) and {out}. Its default needs the existing bend command,
//   which runs in WSL on Windows.
// - A case has a name, a program (a path in the folder of the case list),
//   an input (hex, optional) and an expect (optional):
//   hex (the output bytes), text (the output), or refused (a text that the
//   refusal names). Without expect, all --run must give the same outcome.

// Imports
// =======

import * as child from "node:child_process";
import * as fs from "node:fs";
import * as path from "node:path";

// Types
// =====

type Expect = { hex: string } | { text: string } | { refused: string };

type Case = { name: string; program: string; input?: string; expect?: Expect };

type Options = { runs: string[]; make: string; work: string; cases: string };

type Outcome = { code: number; out: Buffer; err: string };

type Files = { program: string; input?: string };

type Result = { ok: boolean; text: string };

// Constants
// =========

const DEFAULT_MAKE = "bend {source} -o {out}";

const DEFAULT_WORK = path.join(import.meta.dirname, "..", "lean", ".lake", "harness");

const USAGE = "usage: harness.ts --run '<command>' [--run ...] [--make '<command>'] "
  + "[--work <dir>] <cases.json>";

// Functions
// =========

// getOptions args: the options that args name; the case list is the word
// that no flag takes
const getOptions = (args: string[]): Options => {
  const taken = (flag: string): string[] =>
    args.flatMap((a, i) => a === flag ? [args[i + 1] ?? ""] : []);
  const free = args.filter((a, i) => !a.startsWith("--") && !(args[i - 1] ?? "").startsWith("--"));
  return {
    runs: taken("--run"),
    make: taken("--make")[0] ?? DEFAULT_MAKE,
    work: taken("--work")[0] ?? DEFAULT_WORK,
    cases: free[0] ?? "",
  };
};

// getArgv template values: the words of template with each {name} filled; a
// word that names a missing value goes
const getArgv = (template: string, values: Record<string, string | undefined>): string[] =>
  [...template.matchAll(/"([^"]*)"|'([^']*)'|(\S+)/g)]
    .map((m) => m[1] ?? m[2] ?? m[3] ?? "")
    .filter((w) => [...w.matchAll(/\{(\w+)\}/g)].every((m) => values[m[1] as string] !== undefined))
    .map((w) => w.replace(/\{(\w+)\}/g, (_, k: string) => values[k] as string));

// getOutcome argv cwd: what the command did; a command that does not start
// stops the harness
const getOutcome = (argv: string[], cwd: string): Outcome => {
  const run = child.spawnSync(argv[0] as string, argv.slice(1), { cwd });
  if (run.error !== undefined) {
    throw new Error(`cannot start ${argv[0]}: ${run.error.message}`);
  }
  return { code: run.status ?? -1, out: run.stdout, err: run.stderr.toString() };
};

// getShown bytes: the start of bytes, in hex, and its length
const getShown = (bytes: Buffer): string => {
  const start = bytes.subarray(0, 32).toString("hex") + (bytes.length > 32 ? "..." : "");
  return `${start} (${bytes.length} bytes)`;
};

// getFailure c o: why o is not what c expects, or undefined
const getFailure = (c: Case, o: Outcome): string | undefined => {
  const e = c.expect;
  if (e === undefined) {
    return undefined;
  }
  if ("refused" in e) {
    return o.code === 0 ? `gave a result: ${getShown(o.out)}`
      : o.out.length > 0 ? `refused, but wrote ${getShown(o.out)}`
      : o.err.includes(e.refused) ? undefined
      : `refused with: ${o.err.trim().slice(0, 200)}`;
  }
  const want = "hex" in e ? Buffer.from(e.hex, "hex") : Buffer.from(e.text);
  return o.code !== 0 ? `refused: ${o.err.trim().slice(0, 200)}`
    : o.out.equals(want) ? undefined
    : `got ${getShown(o.out)}, want ${getShown(want)}`;
};

// isSame a b: a and b are the same outcome
const isSame = (a: Outcome, b: Outcome): boolean =>
  (a.code === 0) === (b.code === 0) && a.out.equals(b.out);

// tryMake source out o: why make failed to turn source into out, or undefined
const tryMake = (source: string, out: string, o: Options): string | undefined => {
  const made = getOutcome(getArgv(o.make, { source, out }), o.work);
  return made.code === 0 ? undefined : `make failed: ${made.err.trim().slice(0, 200)}`;
};

// writeFiles c i dir o: the files of case number i in the work directory. It
// gives their names, or why the program was not made. A .bend program is made
// where it is, so that its imports resolve; other programs are copied.
const writeFiles = (c: Case, i: number, dir: string, o: Options): Files | string => {
  const file = path.join(dir, c.program);
  const isBend = file.endsWith(".bend");
  const program = isBend ? `${i}.bendtt` : `${i}${path.extname(file)}`;
  if (!isBend) {
    fs.copyFileSync(file, path.join(o.work, program));
  }
  const source = path.relative(o.work, file).split(path.sep).join("/");
  const failure = isBend ? tryMake(source, program, o) : undefined;
  if (failure !== undefined) {
    return failure;
  }
  if (c.input === undefined) {
    return { program };
  }
  fs.writeFileSync(path.join(o.work, `${i}.input`), Buffer.from(c.input, "hex"));
  return { program, input: `${i}.input` };
};

// getResult c i dir o: the result of case number i
const getResult = (c: Case, i: number, dir: string, o: Options): Result => {
  const files = writeFiles(c, i, dir, o);
  if (typeof files === "string") {
    return { ok: false, text: `FAIL ${c.name}: ${files}` };
  }
  const outcomes = o.runs.map((run) => getOutcome(getArgv(run, files), o.work));
  const failures = outcomes.flatMap((x, k) => {
    const why = getFailure(c, x);
    return why === undefined ? [] : [`--run ${k + 1}: ${why}`];
  });
  const lonely = c.expect === undefined && outcomes.length < 2 ? ["no expect, and one --run"] : [];
  const apart = c.expect === undefined && !outcomes.every((x) => isSame(x, outcomes[0] as Outcome))
    ? [`the --run differ: ${outcomes.map((x) => getShown(x.out)).join(" | ")}`] : [];
  const why = [...failures, ...lonely, ...apart];
  return why.length === 0 ? { ok: true, text: `ok   ${c.name}` }
    : { ok: false, text: `FAIL ${c.name}: ${why.join("; ")}` };
};

// getResults o: the results of the case list of o
const getResults = (o: Options): Result[] => {
  const dir = path.dirname(path.resolve(o.cases));
  fs.mkdirSync(o.work, { recursive: true });
  const cases = JSON.parse(fs.readFileSync(o.cases, "utf8")) as Case[];
  return cases.map((c, i) => getResult(c, i, dir, o));
};

// Side effects
// ============

const options = getOptions(process.argv.slice(2));
if (options.runs.length === 0 || options.cases === "") {
  console.error(USAGE);
  process.exit(2);
}
try {
  const results = getResults(options);
  results.forEach((r) => console.log(r.text));
  const passed = results.filter((r) => r.ok).length;
  console.log(`PASS: ${passed} / ${results.length}`);
  process.exit(passed === results.length ? 0 : 1);
} catch (e) {
  console.error(e instanceof Error ? e.message : String(e));
  process.exit(2);
}
