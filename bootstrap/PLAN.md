HEADLINE:
This is a human-written version of PLAN.md. It must NOT be touched by ANY agent for ANY reason and it is the ultimate source of truth for this whole plan. IF THERE IS ANY DRIFT CODE-WISE OR DOCUMENTATION-WISE - THIS IS CORRECT AND I SHOULD BE WARNED IMMEDIATELY. DESPITE WHAT ANY OTHER DOCS MAY SAY: UNTRUSTWORTHY BEND DOES NOT RUN ON WINDOWS OUTSIDE WSL. THERE IS NO BEND-LINT. THIS IS EVEN ABOVE AGENTS.MD AND ANY SKILL.

OUR GOALS:
1 - Our goal is a Bend compiler written in Bend(this doesn't necessarily include creating bend's CHECKER in bend btw) THAT I CAN TRUST(NEVER DISAGREES WITH THE KERNEL ABOUT WHAT THE KERNEL PROVES OR DISPROVES). WE ACCEPT SLOWNESS OR A BEND INTERPRETER-OR-COMPILER WRITTEN IN LEAN ALONG THE WAY. GETTING THIS RIGHT FROM THE START IS AN ABSOLUTE MUST. BEND IS ONLY WHAT THE PROVEN KERNEL GIVES A MEANING TO: EACH DEF WITH A BODY. DEFS WITH NO BODY ARE OUT: F32, EFFECTS, HANDLES, ARRAY ATOMICS.  WHEN WE ADD TO OUR COMPILER (OPTIMIZATIONS, OR FEATURES BEYOND THE PROVEN BEND), THE LAW FOR THE PROVEN BEND (INVARIANTS #1 AND #4) STAYS EXACTLY AS IT IS AND MUST STILL PASS --verdict. SO OUR COMPILER ALWAYS STAYS A PROVEN BEND COMPILER
2 - OUR COMPILER COMPILES TO WASM (WEBASSEMBLY): IT IS SMALL AND HAS AN OFFICIAL FORMAL SPEC. NATIVE MACHINE CODE HAS NO COMPACT FORMAL SPEC, AND C'S MEANING IS HUGE AND FULL OF UNDEFINED BEHAVIOR.

INVARIANTS/LAWS/THEOREMS:
1 - FOR EVERY PROGRAM, NOT ONLY THE ONES THAT THE KERNEL ACCEPTS (SO WE NEED NO BEND COPY OF THE CHECKER): IF THE COMPILED PROGRAM GIVES A RESULT, IT IS THE RESULT THAT `Eval` GIVES. IF `Eval` GIVES A RESULT, THE COMPILED PROGRAM GIVES IT OR RUNS OUT OF MEMORY; WITH ENOUGH MEMORY (#4), IT ALWAYS GIVES IT. SO OUR COMPILER DOES NOT CHECK TYPES: A PROGRAM THAT THE KERNEL REJECTS MAY RUN FOREVER OR GET STUCK, AND ITS OWN LAWS HOLD ONLY AFTER `--verdict` ACCEPTS IT.
2 - THE BEND COPY OF `Eval`, WHICH THE LAWS OF STEP 1 USE, GIVES WHAT THE REAL ONE GIVES, AFTER THE SAME NUMBER OF STEPS, IN BOTH DIRECTIONS (NO EXTRA RESULT, NO MISSING RESULT). A LEAN THEOREM PROVES IT.
3 - A PROGRAM'S `main` TAKES A LIST OF BYTES AND GIVES A LIST OF BYTES: THAT LIST IS ITS RESULT, AND #1 HOLDS FOR EVERY INPUT. IF `Eval`'S FINAL VALUE IS NOT A LIST OF BYTES, BOTH SIDES COUNT AS "NO RESULT".
4 - "ENOUGH MEMORY" IS AT LEAST F BYTES. F IS A FORMULA OF THE PROGRAM'S SIZE, THE INPUT'S SIZE AND THE NUMBER OF STEPS AFTER WHICH `Eval` GIVES THE RESULT. THE LAW FIXES F, SO THE COMPILER CAN'T CHOOSE IT. THIS RULES OUT A COMPILER THAT ALWAYS RUNS OUT OF MEMORY OR NEEDS ABSURD MEMORY, AND IT IS A REAL GUARANTEE ON REAL ENGINES WHENEVER F FITS IN WASM'S 4 GiB. F IS NOT CHOSEN YET.
5 - OUR COMPILER DOES NOT READ .bendtt TEXT. ITS INPUT IS THE BOOK THAT THE KERNEL'S OWN PARSER (`Book.parse`) GIVES FOR THAT TEXT, WRITTEN AS A LIST OF BYTES (#3) BY THE LEAN WRITER (NOT A `partial def`). FOR EVERY BOOK, THE BEND READER, WHICH THE LAWS OF STEP 1 USE, GIVES BACK EXACTLY THAT BOOK FROM THE BYTES THAT THE LEAN WRITER WRITES FOR IT. A LEAN THEOREM PROVES IT.

WHAT WE TRUST:
1 - Lean itself.
2 - The LEAN-VALIDATED, PROVEN-SOUND Bend kernel (`bend2/bendtt.lean`) is the definition of Bend. What it says a program computes IS what the program actually computes. IT IS FIXED: WE CANNOT TOUCH IT IN ANY WAY WHATSOEVER.
3 - From #2 follows that every proof in a Bend program that `--verdict` accepts is true (`--verdict` runs the kernel)
4 - The .bendtt text produced from a .bend file via `bend -o` means what said .bend file says.
5 - A WASM engine follows the WASM spec.
6 - Our Bend copy of WASM's meaning: only the part of WASM that our compiler uses, its binary format included. It is reviewed against the WASM spec and tested with the spec's official test suite. It is not proven, because we know of no Lean or Bend version of the spec. This is a named exception to WHAT WE DON'T TRUST #3.

WHAT WE DON'T TRUST:
1 - The current Bend compiler written in TypeScript.
2 - A checker result without --verdict.
3 - OUR OWN BOOTSTRAP CODE UNTIL IT'S SOMEHOW PROOF-VALIDATED.

STEPS:
1 - We must write BEND LAWS IN BEND'S SYNTAX about >OUR OWN< compiler, so that `--verdict` proves that it is correct by the rules of `Eval`. This is because our compiler is Bend code, and a Bend proof can talk about it directly(a Lean proof could only reason about it from the outside).
2 - We must write a BEND INTERPRETER IN LEAN, with a Lean proof that it gives what `Eval` gives, so that we have a trusted way to RUN >OUR OWN< compiler (it runs any Bend program, ours included). This is because `Eval` is a list of rules, not a program (it can't run anything), we don't trust the current compiler, and our compiler can't run itself before it is compiled.
3 - We must write a LEAN PROOF THAT JOINS #1 AND #2: when the interpreter runs >OUR OWN< compiler, the bytes it writes follow the laws of #1 (it works for any Bend program and its laws, ours included). This is because #1 only says that the compiler is correct by the rules of `Eval`, and #2 only says that the interpreter follows `Eval`. Without this proof, nothing says that the laws hold for what actually runs on the PC.
4 - We must write the BEND COPY of `Eval` and the LEAN PROOF of INVARIANTS #2. This is because Bend can't use Lean's `Eval`, so #1 can only state its laws through a copy. Without this proof, a wrong copy makes #1 prove the wrong thing.
5 - We must write the BEND COPY OF WASM'S MEANING (WHAT WE TRUST #6), so that the laws of #1 can say what a compiled program gives. This is because our compiler compiles to WASM (OUR GOALS #2), and the WASM spec is not written in Bend.
6 - We must write the LEAN WRITER, the BEND READER and the LEAN PROOF of INVARIANTS #5. This is because the kernel's parser is made of `partial def`s, so no Lean theorem can say what it returns, and the kernel is fixed (WHAT WE TRUST #2): a Bend copy of the parser could never be proven to read a text as the kernel does. Without this proof, our compiler could compile a different book than the one the kernel read.

NOTES:
1 - The current UNTRUSTED TypeScript compiler is only a reference guide for ideas.
2 - ALL BOOTSTRAP CODE LIVES STRICTLY INSIDE HERE(BOOTSTRAP FOLDER). DON'T CARE ABOUT REPO GATES OR STUFF LIKE THAT.
3 - PROOF QUALITY DOESN'T MATTER UNLESS PROOFS ARE SO SLOW THEY BLOCK. PROOFS DON'T TAKE PART IN REVIEW SWEEPS UNLESS I TELL YOU TO. LAWS AND THEOREMS (BEND AND LEAN), AND THE DEFINITIONS THEY USE, ON THE OTHER HAND, SHOULD ALWAYS BE DOUBLE-QUESTIONED TO ENSURE THEY REALLY REALLY MATCH MY INTENT; THEN THE LAWS AND THEOREMS ARE PROVEN. THIS DOES NOT MEAN OVERDO LAWS. WE WANT ENOUGH LAWS FOR THE COMPILER TO BE EXACTLY AS SAFE AS IT NEEDS TO BE, NOT MORE NOT LESS.
4 - WORK ONLY IN `bootstrap/refactor`, FULLY ISOLATED FROM THE PREVIOUS BOOTSTRAP ATTEMPT. IT IS NOT IN THIS BRANCH: LOOK INTO THE `old-bootstrap` BRANCH FOR IT. IT MAY ONLY SERVE AS REFERENCE.
5 - THE COMPILED CODE KEEPS ITS STACK IN WASM MEMORY, NOT ON THE ENGINE'S CALL STACK. THE WASM SPEC LETS AN ENGINE STOP A PROGRAM WHEN THE ENGINE'S CALL STACK RUNS OUT, SO MEMORY MUST BE THE ONLY RESOURCE LIMIT (INVARIANTS #4).
6 - Bend guide may serve as reference; same as the untrusted compiler. Things like import dont seem to exist in the kernel for example so are out of scope and not needed for a bootstrap even if ir means a single huge file