HEADLINE:
This is a human-written version of PLAN.md. It must NOT be touched by ANY agent for ANY reason and it is the ultimate source of truth for this whole plan. IF THERE IS ANY DRIFT CODE-WISE OR DOCUMENTATION-WISE - THIS IS CORRECT AND I SHOULD BE WARNED IMMEDIATELY.

OUR GOALS:
1 - Our goal is a Bend compiler written in Bend(this doesn't necessarily include creating bend's CHECKER in bend btw) THAT I CAN TRUST(NEVER DISAGREES WITH THE KERNEL ABOUT WHAT THE KERNEL PROVES OR DISPROVES). WE ACCEPT SLOWNESS OR A BEND INTERPRETER-OR-COMPILER WRITTEN IN LEAN ALONG THE WAY. GETTING THIS RIGHT FROM THE START IS AN ABSOLUTE MUST.

WHAT WE TRUST:
1 - Lean itself.
2 - The LEAN-VALIDATED, PROVEN-SOUND Bend kernel (`bend2/bendtt.lean`) is the definition of Bend. What it says a program computes IS what the program actually computes.
3 - From #2 follows that every proof in a Bend program that `--verdict` accepts is true (`--verdict` runs the kernel)
4 - The .bendtt text produced from a .bend file via `bend -o` means what said .bend file says.

WHAT WE DON'T TRUST:
1 - The current Bend compiler written in TypeScript.
2 - A checker result without --verdict.

STEPS:
1 - 

NOTES:
1 - The current UNTRUSTED TypeScript compiler is only a reference guide for ideas.
2 - EVERY BOOTSTRAP CODE LIVES STRICTLY INSIDE HERE(BOOTSTRAP FOLDER). DON'T CARE ABOUT REPO GATES OR STUFF LIKE THAT.