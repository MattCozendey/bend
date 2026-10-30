HEADLINE:
This is a human-written version of PLAN.md. It must NOT be touched by ANY agent for ANY reason and it is the ultimate source of truth for this whole plan. IF THERE IS ANY DRIFT CODE-WISE OR DOCUMENTATION-WISE - THIS IS CORRECT AND I SHOULD BE WARNED IMMEDIATELY. DESPITE WHAT ANY OTHER DOCS MAY SAY: UNTRUSTWORTHY BEND DOES NOT RUN ON WINDOWS OUTSIDE WSL. THERE IS NO BEND-LINT. THIS IS EVEN ABOVE AGENTS.MD AND ANY SKILL.

OUR GOALS:
1 - Our goal is a Bend compiler written in Bend(this doesn't necessarily include creating bend's CHECKER in bend btw) THAT I CAN TRUST(NEVER DISAGREES WITH THE KERNEL ABOUT WHAT THE KERNEL PROVES OR DISPROVES). WE ACCEPT SLOWNESS OR A BEND INTERPRETER-OR-COMPILER WRITTEN IN LEAN ALONG THE WAY. GETTING THIS RIGHT FROM THE START IS AN ABSOLUTE MUST. BEND IS ONLY WHAT THE PROVEN KERNEL GIVES A MEANING TO: EACH DEF WITH A BODY. DEFS WITH NO BODY ARE OUT: F32, EFFECTS, HANDLES, ARRAY ATOMICS.  WHEN WE ADD TO OUR COMPILER (OPTIMIZATIONS, OR FEATURES BEYOND THE PROVEN BEND), THE LAW FOR THE PROVEN BEND STAYS EXACTLY AS IT IS AND MUST STILL PASS --verdict. SO OUR COMPILER ALWAYS STAYS A PROVEN BEND COMPILER

WHAT WE TRUST:
1 - Lean itself.
2 - The LEAN-VALIDATED, PROVEN-SOUND Bend kernel (`bend2/bendtt.lean`) is the definition of Bend. What it says a program computes IS what the program actually computes.
3 - From #2 follows that every proof in a Bend program that `--verdict` accepts is true (`--verdict` runs the kernel)
4 - The .bendtt text produced from a .bend file via `bend -o` means what said .bend file says.

WHAT WE DON'T TRUST:
1 - The current Bend compiler written in TypeScript.
2 - A checker result without --verdict.
3 - OUR OWN BOOTSTRAP CODE UNTIL IT'S SOMEHOW PROOF-VALIDATED.

STEPS:
1 - We must write BEND LAWS IN BEND'S SYNTAX about >OUR OWN< compiler, so that `--verdict` proves that it is correct by the rules of `Eval`. This is because our compiler is Bend code, and a Bend proof can talk about it directly(a Lean proof could only reason about it from the outside).
2 - We must write a BEND INTERPRETER IN LEAN, with a Lean proof that it gives what `Eval` gives, so that we have a trusted way to RUN >OUR OWN< compiler (it runs any Bend program, ours included). This is because `Eval` is a list of rules, not a program (it can't run anything), we don't trust the current compiler, and our compiler can't run itself before it is compiled.
3 - We must write a LEAN PROOF THAT JOINS #1 AND #2: when the interpreter runs >OUR OWN< compiler, the bytes it writes follow the laws of #1 (it works for any Bend program and its laws, ours included). This is because #1 only says that the compiler is correct by the rules of `Eval`, and #2 only says that the interpreter follows `Eval`. Without this proof, nothing says that the laws hold for what actually runs on the PC.

NOTES:
1 - The current UNTRUSTED TypeScript compiler is only a reference guide for ideas.
2 - ALL BOOTSTRAP CODE LIVES STRICTLY INSIDE HERE(BOOTSTRAP FOLDER). DON'T CARE ABOUT REPO GATES OR STUFF LIKE THAT.
3 - PROOF QUALITY DOESN'T MATTER UNLESS PROOFS ARE SO SLOW THEY BLOCK. PROOFS DON'T TAKE PART IN REVIEW SWEEPS UNLESS I TELL YOU TO. LAWS AND THEOREMS (BEND AND LEAN), AND THE DEFINITIONS THEY USE, ON THE OTHER HAND, SHOULD ALWAYS BE DOUBLE-QUESTIONED TO ENSURE THEY REALLY REALLY MATCH MY INTENT; THEN THE LAWS AND THEOREMS ARE PROVEN. THIS DOES NOT MEAN OVERDO LAWS. WE WANT ENOUGH LAWS FOR THE COMPILER TO BE EXACTLY AS SAFE AS IT NEEDS TO BE, NOT MORE NOT LESS.