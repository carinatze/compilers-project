I built an optimizing ahead-of-time compiler from a high-level language with functional and imperative features to x86-64. This milestone introduces the procedure return abstraction and non-tail calls, so that we can call functions that return values to non-tail contexts.
This branch provides the skeleton for CPSC 411 Milestone 6: https://www.students.cs.ubc.ca/~cs-411/2022w2/a6_milestone_top.html

When submitting, you should ensure the name of the `compiler.rkt` file and the
provides from that file are the same as in this commit.
You may change the code base in any other way, including moving code to other
files, as long as `compiler.rkt` reprovides the appropriate functions.
You can check this is the case by running `raco test interface-test.rkt`.

Exercise 5, impose-calling-conventions and impose-calling-conventions tests -> impose-calling-conventions.rkt

Exercise 6, select-instructions and select-instructions tests -> select-instructions.rkt

Exercise 7, uncover-locals and uncover-locals tests -> uncover-locals.rkt

Exercise 5, impose-calling-conventions and impose-calling-conventions tests -> impose-calling-conventions.rkt

Exercise 8, undead-analysis and undead-analysis tests -> undead-analysis.rkt

Exercise 9, conflict-analysis and conflict-analysis tests -> conflict-analysis.rkt

Exercise 11, allocate-frames and allocate-frames tests -> allocate-frames.rkt

Exercise 14, replace-locations and replace-locations tests -> replace-locations.rkt

Exercise 17, implement-fvars and implement-fvars tests -> implement-fvars.rkt

Exercise 19, generate-x64 and generate-x64 tests -> generate-x64.rkt

----------------- incomplete --------------------
Exercise 2, uniquify -> compiler.rkt

Exercise 3, sequentialize-let -> compiler.rkt

Exercise 4, normalize-bind -> compiler.rkt

Exercise 10, assign-call-undead-variables -> compiler.rkt

Exercise 12, assign-registers -> compiler.rkt

Exercise 13, assign-frame-variables -> compiler.rkt

Exercise 15, optimize-predicates -> compiler.rkt

Exercise 16, expose-basic-blocks -> compiler.rkt

Exercise 18, patch-instructions -> compiler.rkt
