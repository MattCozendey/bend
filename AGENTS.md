# AGENTS

Contribution guidelines, for agents and humans alike.

The rules stated here have priority over any and all rules in any skill file or tool(UNLESS EXPLICITLY TOLD BY A HUMAN OTHERWISE PER SESSION, WHICH MUST NOT BE STORED)

## 0. Core

- If a skill does not load, read its file in `.agents/skills/`.
- Do not change any `.md` file without asking me.

## 1. Communication

- Speak the language you are spoken to; but shortly and without dropping important information in
  ASD-STE100 (or the language's equivalent), with learnings from the `i-have-adhd`.
- Use a global counter for your non-trivial questions that grows through the session. Repeat each
  open question in each response until I answer it or tell you to use common sense.

## 2. Code

These rules hold for every language.

### Tools

- Do not work around a lint rule. Suppress/expect a finding only with a directive whose reason says why
  (for example, a measurement).
- When a deterministic tool and a skill disagree, obey the tool.
- Before you show me your changes, do sweeps. A sweep:
  1. Reads each changed area once with `thermo-nuclear-code-quality-review` and `erasure`, and the
     changed functions with `cyclomatic-complexity`. It fixes what they find.
  2. Runs the project's lint and type check until they pass.
  3. Commits its in-area changes, then its cross-area changes.

  Sweep 1 reads the branch diff from its base. Before each later sweep, ask me if it reads the
  whole repo, the whole diff, or the delta (the hunks changed since the previous sweep, and their
  callers). Repeat until a sweep finds nothing to delete, no structural regression, no missed large
  simplification and no spaghetti growth. After sweep 3, stop and ask me.

- A file over 1000 lines can be fine. Ask me before you split one.

### Documentation

- Give each fact one location. A comment must not repeat what the docs state or clearly imply.

### Checks

- Ask me before you write a check. Check only a property that matters, never an implementation
  detail.
- Do not try to check that generated data, or a copy of a standard's text, matches its source with
  our own code. Check generated data with a test against an independent source (for example,
  another implementation, or the standard's own test vectors). That test does not replace the
  checks of the code. Tell me which copies of standard text you changed, so that I can check them.

### Bend

Follow the `bend2` skill. In this project:

- Before you build or test, run `bend version` in the shell that you build in. As of 2026-10-28,
  Bend does not run natively on Windows; a build with the build tag `win` (`bend <version>+win`)
  is a fork that does. On Windows, run Bend natively only with such a build; otherwise, use Bend in
  WSL. If no shell has a Bend that fits, stop and ask me. When you report a result, give the shell
  and the `bend version` that ran.
- Do not change, update or rebuild Bend. Modify a fork only when I expressly allow it, and only for
  a bug that its Windows support caused.
- Bend code must pass bend-lint (configured in `bend-lint.json`): `bun run lint` must add no
  finding. `bunx bend-lint --fix-dangerously <file>` formats a file.
- A module is a folder in `src/`. Its files:
  - `impl.bend`: its entrypoint, and the only file that it must have. Prefer to keep all of its
    implementation in this file. Other implementation files can exist; they do not contain laws.
  - `shared.bend` (optional): what its implementation or test files have in common. It does not
    contain laws.
  - `spec.bend` (optional): its laws.
  - `tests.bend` (optional): its tests, of the properties of the module that a law cannot state.
- `src/shared/` is the module for helpers that are too small for a module of their own (for
  example, with no effects, or too simple to matter).

### TypeScript

- Write functional code without mutation, except when speed is a priority for a file (ask me);
  wherein any and all optimization opportunities are fair game.
- Lay out each file in this order, with a comment before each section (if the section is needed):
  imports, types, constants, functions, side effects.
- Write functions as `const` arrow functions.
- Inline a helper that has only one caller; extract one only when it has more than one.
- Name a function by what it gives: `get…` for a value (`getRecord`), `is…` or `has…` for a Bool
  (`isSpan`). Name one that gives nothing by what it does (`writeFiles`, `prune`). `try…` catches
  what it calls, and gives the failure as a value (`undefined`, or a Result) or skips it. The type,
  not the name, says that a value can be `undefined`. Constants are SCREAMING_SNAKE_CASE, types
  PascalCase, other names camelCase. `result.ts` keeps the names of its Result (`ok`, `error`,
  `wrap`, `unwrap`).
- Do not use barrel exports or re-exports (`export { x } from "..."`, `export * from "..."`). Import
  each name from the module that exports it.