---
title: Layered Concurrent Programs
nav_order: 2
---

Civl takes as input a *layered concurrent program*.
A layered concurrent program represents a sequence of concurrent programs, from most concrete (e.g., a low-level implementation) to most abstract (e.g., a high-level specification).
Civl verifies a layered concurrent program by verifying each layer and the connection between adjacent layers separately.

In this section we show a basic example to explain how a layered concurrent program represents a sequence of increasingly simpler concurrent programs.
Understanding this foundational aspect of Civl will make it easier to understand everything explained later.

## A Simple Layered Concurrent Program

```boogie
var {:layer 0,2} x: int;

pure action Add(a: int, b: int) returns (c: int)
{ c := a + b; }

yield procedure {:layer 0} Incr(val: int)
refines AtomicIncr;
{
  call {:layer 0} x := Add(x, val);
}
left action {:layer 1} AtomicIncr(val: int)
modifies x;
{ x := x + val; }

yield procedure {:layer 1} IncrBy2()
refines AtomicIncrBy2;
{
  par Incr(1) | Incr(1);
}
atomic action {:layer 2} AtomicIncrBy2()
modifies x;
{ x := x + 2; }

yield procedure {:layer 2} Main()
{
  call IncrBy2();
}
```

The program above represents three concurrent programs, at layers 0, 1, and 2, that share parts of their code.
Layer 0 is the most concrete and layer 2 is the most abstract.
The annotation `{:layer 0,2}` on global variable `x` is a range of layers from 0 to 2 indicating that `x` exists at all layers in this layer range.
The global variable `x` is introduced at layer 0 via a call to the pure action `Add` and hidden at layer 2.
Introduction and hiding of global and local variables is explained in detail in a
[later section](#introducing-and-hiding-variables).
The annotation `{:layer 0}` on `Incr` indicates that 0 is the highest layer on which `Incr` exists.
The annotation `refines AtomicIncr` on `Incr` indicates that on layers greater than 0 a call to `Incr` is rewritten to a call to `AtomicIncr`.
Similarly, procedure `IncrBy2` exists on layers 1 and lower and is replaced by `AtomicIncrBy` at layers above 1.

### Program at Layer 0

```boogie
var x: int;

pure action Add(a: int, b: int) returns (c: int)
{ c := a + b; }

yield procedure Incr(val: int)
{
  call x := Add(x, val);
}

yield procedure IncrBy2()
{
  par Incr(1) | Incr(1);
}

yield procedure Main()
{
  call IncrBy2();
}
```

The layer 0 program is shown above.
Procedure `IncrBy2` creates two tasks via a parallel call to `Incr`, each instance of which
makes a single call to the atomic action `Intro_x`.
Preemptions can occur at entry into or exit from `Main`, `IncrBy2`, or `Incr`.

### Program at Layer 1

```boogie
var x: int;

atomic action AtomicIncr(val: int)
modifies x;
{ x := x + val; }

yield procedure IncrBy2()
{
  call AtomicIncr(1);
  call AtomicIncr(1);
}

yield procedure Main()
{
  call IncrBy2();
}
```

In the layer 1 program, shown above, the parallel call to `Incr` is rewritten to a sequence of calls to `AtomicIncr`.
The justification for this rewrite is that `Incr` refines `AtomicIncr` and `AtomicIncr` is a left mover.
Explanation for these concepts is presented later.

The implementation of yield procedures at layer 0 is often omitted.
In this case, the layer 0 program is not defined.
The atomic actions refined by layer 0 procedures are considered primitive atomic actions used
to define the semantics of the (lowest) layer 1 program.

### Program at Layer 2

```boogie
var x: int;

atomic action AtomicIncrBy2()
modifies x;
{ x := x + 2; }

yield procedure Main()
{
  call AtomicIncrBy2();
}
```

In the layer 2 program, shown above, the call to procedure `IncrBy2` in `Main` is rewritten to a call to atomic action `AtomicIncrBy2`.
The justification for this rewrite is that `IncrBy2` refines `AtomicIncrBy2`.

## Layer Checking

The well-formedness of a layered concurrent program is governed by a set of layer checking rules.
These rules ensure that the individual program layers can be extracted and that the verification guarantees are justified.
We can loosely distinguish between "data layering" and "control layering".

Data layering concerns the variables (both global and local) that exist on each layer.
In the example above, both global variable `x` and local variable `val` (the input parameter to `Incr` and `AtomicIncr`) exist on all program layers.
In a [different section](https://civl-verifier.github.io/introducing-hiding-variables.html) we show how variables can be introduced and hidden, such that different layers have different variables.

Control layering concerns the actions and yielding procedures that exist on each layer.
This aspect controls how the bodies of yielding procedures change across layers.
In a layered concurrent program, atomic actions cannot be called directly.
Instead, yielding procedures can call other yielding procedures.
For example, recall that `IncrBy2` in the layered program above makes calls to procedure `Incr`, as opposed to `AtomicIncr`.
In the layer 0 program we still see this call to `Incr`.
Then, since `Incr` disappears at layer 0 and is abstracted by `AtomicIncr`, we see these calls replaced by calls to `AtomicIncr` in the layer 1 program.
In general, a yielding procedure that disappears at layer `n` cannot make calls to yielding procedures that disappear on a layer greater than `n`.
The simple case is that there are only calls to procedures that disappear on layers smaller than `n`.
Then there are only calls to atomic actions left at layer `n`.

Data layering and control layering obviously interact, since the variables accessed by the control of a particular layer must indeed exist on that layer.

## Semantics

Civl considers two semantics for a concurrent program---*preemptive* and *non-preemptive*.
The preemptive semantics is the standard interleaving semantics, where context switches can happen at any time between the execution of atomic actions.
This semantics models the actual behaviors of the concurrent program that we want to verify.
In contrast, the non-preemptive semantics allows a context switch only at the entry to or return from a procedure
and at a call to a [yield invariant](https://civl-verifier.github.io/yield-invariants.html).
In particular, a context switch is not introduced just before or just after executing an atomic action.
The non-preemptive semantics simplifies reasoning, because fewer interleavings have to be considered.
Civl justifies going from the preemptive to the non-preemptive semantics using
[mover types](https://civl-verifier.github.io/mover-types.html).

A program location where a context switch may happen is called a *yield location*.
Any execution path in a procedure from its entry to its exit is
partitioned into a sequence of execution fragments from one yield location to the next.
Each such execution fragment is called a *yield-to-yield fragment*.
Notice that these yield-to-yield fragments are dynamically scoped.
Yield locations specify the non-preemptive semantics.
Civl checks that there are "sufficiently many" yield locations such that reasoning about the non-preemptive semantics
is sufficient to reason about the preemptive semantics.

Going from preemptive to non-preemptive semantics simplifies the reasoning at one particular program layer.
In going from the layer 0 program to the layer 2 program, the set of yield locations progressively reduces because invocations of yielding procedures are replaced by invocations of atomic actions, thereby leading to simplified reasoning at the higher layer.
