This is a human-written version of PLAN.md. It must NOT be touched by ANY agent for ANY reason and it is the ultimate source of truth for this whole plan.

WHAT WE TRUST:
1 - Lean itself.
2 - The LEAN-VALIDATED, PROVEN-SOUND Bend kernel (`bend2/bendtt.lean`) is the definition of Bend. What it says a program computes IS what the program actually computes.
3 - From #2 follows that every proof in a Bend program that --verdict accepts is true(--verdict runs the kernel)
4 - The .bendtt text produced from a .bend file via `bend -o` means what said .bend file says.

WHAT WE DON'T TRUST:
1 - The current Bend compiler written in Typescript.
2 - A checker result without --verdict.