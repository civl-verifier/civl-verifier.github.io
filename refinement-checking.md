---
title: Refinement Checking
nav_order: 4
---

We now explain how the specification `refines AtomicIncrBy2` is checked on the implementation of the procedure `IncrBy2`.
This refinement checking justifies the transformation of the layer-1 program to the layer-2 program.
Civl checks that along each execution path in `IncrBy2` from entry to exit, there is exactly one yield-to-yield fragment that behaves like `AtomicIncrBy2`.
(In this particular example, `IncrBy2` consists of only a single yield-to-yield fragment at layer 1.)
All other yield-to-yield fragments before and after this unique fragment leave state visible to the environment of `IncrBy2` unchanged.
The visible state for `IncrBy2` includes only the global variable `x`.
In general, visible state for a procedure includes global variables and output variables of the procedure.

The signature of a procedure and its refined action must match unless a parameter of the procedure is annotated with `:hide` in
which case this parameter may be omitted from the signature of the refined action.
If a global variable is hidden at the disappearing layer of a procedure, then the visible state over which refinement is
checked does not include this variable.
Similary, any output parameter of the procedure annotated with `:hide` is excluded from the visible state.

If a yield procedure omits the refines clause, it is expected to refine the SKIP action.
This is tantamount to annotating each parameter of the procedure with `:hide`.
Since the SKIP action does not modify any variable, every yield-to-yield fragment in the procedure is allowed to modify
only those global variables that are hidden at the disappearing layer of the procedure.