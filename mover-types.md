---
title: Mover Types
nav_order: 5
---

In this section, we explain how Civl exploits commutativity of atomic actions to justify reasoning about non-preemptive semantics at each layer.
Civl allows each atomic action to be labeled by one of four mover types: `atomic`, `left`, `right`, and `both`.
The following code illustrates mover types for atomic actions.

```boogie
var {:layer 0,1} x:int;

yield invariant {:layer 1} yield_x(n: int);
preserves x >= n;

yield procedure {:layer 0} Incr(val: int);
refines AtomicIncr;
both action {:layer 1} AtomicIncr(val: int)
modifies x;
{ x := x + val; }

yield procedure {:layer 1} p()
requires call yield_x(5);
ensures call yield_x(8);
{
  call Incr(1);
  call Incr(1);
  call Incr(1);
}
```

The atomic action `AtomicIncr` is labeled with the mover type `both`, indicating that it is both a left mover and a right mover.
Consequently, the calls to `Incr` in `p` do not have to be separated by a yield.
The calls to `Incr` in `p` commute with atomic actions executed by other threads so that they all appear to execute together.
The use of mover types leads to fewer yields and more efficient verification of the body of `p`.

In general, Civl checks that the sequence of mover types of the atomic actions in every yield-to-yield fragment matches the expression `(right-mover)*;(non-mover)?;(left-mover)*`, i.e., a sequence of right movers, followed by at most one non-mover, followed by a sequence of left movers.
The mover types of atomic actions are validated using pairwise commutativity checks between all atomic actions that exist together on some layer.

## Mover Procedures

Sometimes it can be convenient to reason about a yielding procedure without abstracting it to an atomic action.
For this purpose, Civl supports *mover procedures*, which we illustrate in the following example.

```boogie
var {:layer 0,2} x : int;

yield left procedure {:layer 1} inc(i : int)
modifies x;
requires {:layer 1} i >= 0;
ensures {:layer 1} x == old(x) + i;
{
  if (i > 0)
  {
    call inc_x(1);
    call inc(i-1);
  }
}

yield procedure {:layer 0} inc_x(n: int);
refines atomic_inc_x;
both action {:layer 1} atomic_inc_x(n: int)
modifies x;
{ x := x + n; }
```

In the program above, the mover procedure `inc` is annotated with the mover type `left`.
This annotation is applicable to `inc` only at its disappearing layer 1.
This annotation indicates that, at layer 1, any execution of the implementation of `inc` can be considered an indivisible computation that behaves like a left mover and is summarized by the layer-1 preconditions and postconditions of `inc`.
A mover procedure that disappears at layer `n` can only be called by yielding procedures that also disappear at layer `n`.

## Abstraction aids Commutativity

Often, a program may use atomic actions that are neither right nor left movers and hence cannot be commuted with actions performed by other threads.
However, it may be possible to create abstractions of the program's atomic actions so that important actions achieve a commuting mover type.

```boogie
var {:layer 0,2} x:int;

yield procedure {:layer 0} Incr(val: int);
refines AtomicIncr;
atomic action {:layer 1} AtomicIncr(val: int)
modifies x;
{ x := x + val; }

yield procedure {:layer 0} Read() returns (v: int);
refines AtomicRead;
atomic action {:layer 1} AtomicRead() returns (v: int)
{ v := x; }

yield procedure {:layer 1} _Incr(val: int)
refines AbstractAtomicIncr;
{
  call Incr(val);
}
right action {:layer 2} AbstractAtomicIncr(val: int)
{ assert 0 <= val; x := x + val; }

yield procedure {:layer 1} _Read() returns (v: int)
refines AbstractAtomicRead;
{
  call Read();
}
left action {:layer 2} AbstractAtomicRead() returns (v: int)
{ assume x <= v; }
```

In the code above, atomic actions `AtomicIncr` and `AtomicRead` at layer 1 are neither right nor left movers.
At layer 2, we create abstractions `AbstractAtomicIncr` and `AbstractAtomicRead` of `AtomicIncr` and `AtomicRead` respectively.
The abstractions are chosen so that `AbstractAtomicIncr` is a right mover and `AbstractAtomicRead` is a left mover.