---
title: Yield Invariants
nav_order: 6
---

Reasoning about concurrent programs is difficult because of the
possibility of interference among concurrently-executing procedures.
Invariants are useful to express the possible interference and thus
set up the context for refinement checking.
Civl introduces yield invariants, a specification idiom that allows the programmer to factor out similar noninterference specifications into a single named and parameterized specification.

```boogie
var {:layer 0,1} x:int;

yield procedure {:layer 0} Incr(val: int);
refines AtomicIncr;
atomic action {:layer 1} AtomicIncr(val: int)
modifies x;
{ x := x + val; }

yield invariant {:layer 1} yield_x(n: int);
preserves x >= n;

yield procedure {:layer 1} p()
requires call yield_x(old(x));
ensures call yield_x(old(x)+3);
{
  call Incr(1);
  call yield_x(x);
  call Incr(1);
  call yield_x(x);
  call Incr(1);
}

yield procedure {:layer 1} q()
preserves call yield_x(old(x));
{
  while (*)
  invariant {:yields} true;
  invariant call yield_x(old(x));
  {
    call Incr(3);
  }
}
```

The yield invariant `yield_x` is parameterized by `n` and states that the global variable `x` is no smaller than `n`.
To use `yield_x`, the caller must supply an argument for the parameter `n`.
There are six invocations of `yield_x` in the program, 4 in `p` and 2 in `q`.
Let us first understand how `p` uses `yield_x`.

Procedure `p` invokes `yield_x` at entry using the annotation `requires call yield_x(old(x))` indicating that `old(x)` is passed for parameter `n`.
The expression `old(x)` refers to the value of `x` just before `p` is invoked.
The caller of `p` must ensure that `yield_x(old(x))` holds at entry to `p`, which is trivial given the meaning of `old(x)`.
Procedure `p` also invokes `yield_x` at exit using the annotation `ensures call yield_x(old(x)+3)`, guaranteeing that `yield_x(old(x) + 3)` must hold at exit from `p`.

Procedure `q` uses the annotation `preserves call yield_x(old(x))` which is a shorthand for a pair of annotations `requires call yield_x(old(x))` and `ensures call yield_x(old(x))`.
Procedure `q` also uses `invariant call yield_x(old(x))` to supply the noninterference condition at the yield at the head of the loop in `q`.
