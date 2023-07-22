# Compilers Construction Project 
I built an optimizing ahead-of-time compiler from a high-level language with functional and imperative features to x86-64. The project proceeds bottom-up. We start with the "lowest" level of abstraction, assembly language, and gradually design and implement new layers of abstraction as languages. (Source: https://www.students.cs.ubc.ca/~cs-411/2022w2/milestone_top.html) This milestone handles procedure return abstraction and non-tail calls, so that we can call functions that return values to non-tail contexts.
This branch provides the skeleton for CPSC 411 Milestone 6: https://www.students.cs.ubc.ca/~cs-411/2022w2/a6_milestone_top.html

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
