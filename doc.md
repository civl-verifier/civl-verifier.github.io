---
title: Civl Tutorial
---

[Civl Syntax](#civl-syntax)

[Layered Concurrent Programs](#layered-concurrent-programs)

[Introducing and Hiding Variables](#introducing-and-hiding-variables)

[Refinement Checking](#refinement-checking)

[Mover Types](#mover-types)

[Yield Invariants](#yield-invariants)

[Linear Typing and Permissions](#linear-typing-and-permissions)

[Summarizing Asynchrony](#summarizing-asynchrony)

# Civl Syntax

Civl is an extension of Boogie. In Boogie, (almost every) abstract syntax tree
node can be annotated with attributes of the form `{:attr e1, e2, ...}`, where
`attr` is the attribute name and `e1, e2, ...` are expressions (denoting
parameters of the attribute). Running `boogie -attrHelp` prints all supported attributes.
Civl programs are specified using syntactic extensions to Boogie as well as attributes.
This section provides a brief overview of Civl syntax.

## Types, Functions, Constants

Types, functions, and constants are declared just as in Boogie.

## Global Variables

Global variables have a *layer range*.

```boogie
var {:layer 0,10} x:int;
```

Global variable `x` is *introduced* at layer `0` and *hidden* at layer `10`. We
call `0` the *introduction/lower layer* of `x`, and `10` the *disappearing/upper
layer* of `x`.
The layer range `{:layer n}` on a global variable is identical to `{:layer n,n}`.

## Actions

*Atomic actions* are the building blocks of a Civl program, encapsulating all
accesses to global variables.

An atomic action typically has a *mover type* and a *layer range*. The mover type is
either `atomic` (non-mover), `right` (right mover), `left` (left mover), or
`both` (both mover). The body of an atomic action consists of a sequence of
assert commands, called the *gate*, followed by a loop-free block of
code, denoting a *transition relation*.

```boogie
atomic action {:layer 2,5} FOO (i: int) returns (j: int)
modifies x;
{
  assert x > 0;
  j := x;
  x := x + i;
}
```

Atomic action `FOO` is *available* from layer `2` up to layer `5` (*introduced*
at layer `2` and *disappearing* at layer `5`). The gate of `FOO` is `x > 0`, and the
transition relation states that output parameter `j` returns the current value
of global variable `x`, and the value of input parameter `i` is added to `x`.
The layer range `{:layer n}` on an action is identical to `{:layer n,n}`.
Actions may call other actions as long as the call graph is acyclic
and for each call the caller's layer range is contained in the callee's layer range.

It is possible to declare an atomic action without a mover type.
Civl does not add such an action to the pool of actions over which the checking
of mover types is performed.
Consequently, such actions are used in a restricted manner, notably for linking
two layers across which the set of global variables differ and for providing
auxiliary invariants and abstractions as proof hints.

## Yield Invariants

A *yield invariant* has a layer number and a sequence of `invariant` clauses (but
no body).

```boogie
yield invariant {:layer 1} yield_x(i: int);
invariat i <= x;
```

Yield invariant `yield_x` states that global variable `x` is greater than or
equal to parameter `i`.

## Yielding Procedures

Yielding procedures describe the actual concurrent program.
There are two kinds: *action procedures* that get summarized
by atomic actions, and *mover procedures* that get summarized by
pre/postconditions.

### Action Procedure

An action procedure has a *disappearing layer* and a *refined atomic action*.
The `modifies` clause is implicit and contains all global variables.

```boogie
yield procedure {:layer 1} foo (...) returns (...);
refines FOO;
```

Action procedure `foo` *disappears* at layer `1` and *refines* the atomic action
`FOO`.

If no `refines` clause is given, then the procedure is called a
*skip procedure* which refines the implicitly declared atomic action `SKIP`.

```boogie
both action {:layer 0,∞} SKIP () { }
```

### Mover Procedure

A mover procedure has a *disappearing layer* and a *mover type*. The `modifies`
clause has to be provided.

```boogie
yield right procedure {:layer 1} foo (...) returns (...);
modifies ...;
```

## Implementations

The implementations (i.e., bodies) of yielding procedures support the following
additional commands.

* **Parallel call**: `par i := A(j) | k := B(l)`
* **Asynchronous call**: `async call A(i)`

## Specifications

Every precondition, postcondition, assertion, and loop invariant is annotated
with a list of layer numbers (`{:layer l1, l2, ...}`).

Yield invariants can be invoked in calls, parallel calls, as preconditions
(`requires call`), postconditions (`ensures call`), and loop invariants
(`invariant call`).

Every loop is either *non-yielding* or *yielding* (denoted with `:yields` on a
loop invariant with condition `true`).

A call may be annotated with `:mark`.

## Parameters

Every input and output parameter of a yielding procedure has a layer range.
Implicitly, it ranges from the lowest layer up to the disappearing layer of the
procedure. A different layer range can be assigned to every parameter using the
`:layer` attribute.

Parameters of action procedures can be annotated with `:hide` to declare that
the parameter does not occur in the refined atomic action.

## Pure Procedures

Pure procedures do not read or modify global variables.
These procedures support the injection of (potentially unverified) facts and proof hints.
In particular, this is a useful alternative to global quantified axioms.

```boogie
pure procedure Lemma_add_to_set (x: X, set: [X]bool);
requires !set[x];
ensures card(set[x := true]) == card(set) + 1;
```

The pure procedure `Lemma_add_to_set` states the fact about set cardinality,
that adding an element to a set increases the sets cardinality by one.

# Layered Concurrent Programs

Civl takes as input a *layered concurrent program*.
A layered concurrent program represents a sequence of concurrent programs, from most concrete (e.g., a low-level implementation) to most abstract (e.g., a high-level specification).
Civl verifies a layered concurrent program by verifying each layer and the connection between adjacent layers separately.

In this section we show a basic example to explain how a layered concurrent program represents a sequence of increasingly simpler concurrent programs.
Understanding this foundational aspect of Civl will make it easier to understand everything explained later.

## A Simple Layered Concurrent Program

```boogie
var {:layer 0,2} x: int;

action {:layer 0} Intro_x(val: int)
modifies x;
{ x := x + val; }

yield procedure {:layer 0} Incr(val: int)
refines AtomicIncr;
{
  call Intro_x(val);
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
The global variable `x` is introduced at layer 0 via the action `Intro_x` and hidden at layer 2.
Introduction and hiding of global and local variables is explained in detail in a
[later section](#introducing-and-hiding-variables).
The annotation `{:layer 0}` on `Incr` indicates that 0 is the highest layer on which `Incr` exists.
The annotation `refines AtomicIncr` on `Incr` indicates that on layers greater than 0 a call to `Incr` is rewritten to a call to `AtomicIncr`.
Similarly, procedure `IncrBy2` exists on layers 1 and lower and is replaced by `AtomicIncrBy` at layers above 1.

### Program at Layer 0

```boogie
var x: int;

action Intro_x(val: int)
modifies x;
{ x := x + val; }

yield procedure Incr(val: int)
{
  call Intro_x(val);
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

The layer-0 program is shown above.
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

In the layer-1 program, shown above, the parallel call to `Incr` is rewritten to a sequence of calls to `AtomicIncr`.
The justification for this rewrite is that `Incr` refines `AtomicIncr` and `AtomicIncr` is a left mover.
Explanation for these concepts is presented later.

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

In the layer-2 program, shown above, the call to procedure `IncrBy2` in `Main` is rewritten to a call to atomic action `AtomicIncrBy2`.
The justification for this rewrite is that `IncrBy2` refines `AtomicIncrBy2`.

## Layer Checking

The well-formedness of a layered concurrent programs is governed by a set of layer type-checking rules.
These rules ensure that the individual program layers can be extracted and that the verification guarantees are justified.
We can loosely distinguish between "data layering" and "control layering".

Data layering concernes the variables (both global and local) that exist on each layer.
In the example above, both global variable `x` and local variable `val` (the input parameter to `Incr` and `AtomicIncr`) exist on all program layers.
In a [later section](#introducing-and-hiding-variables) we show how variables can be introduced and hidden, such that different layers have different state.

Control layering concerns the actions and yielding procedures that exist on each layer.
As one of the most central aspects of Civl, this controls how the bodies of yielding procedures changes across layers.
In a layered concurrent program, atomic actions cannot be called directly.
Instead, yielding procedures can call other yielding procedures.
For example, recall that `IncrBy2` in the layered program above makes calls to procedure `Incr`, as opposed to `AtomicIncr`.
In the layer 0 program we still see this calls to `Incr`.
Then, since `Incr` disappears at layer 0 and is abstracted by `AtomicIncr`, we see these calls replaced by calls to `AtomicIncr` in the layer 1 program.
In general, a yielding procedure that disappears at layer `n` cannot make calls to yielding procedures that disappear on a layer greater than `n`.
The simple case is that there are only calls to procedures that disappear on layers smaller than `n`.
Then there are only calls to atomic actions left at layer `n`.
There are only three exceptions when a yielding procedure can make calls to another yielding procedure with the same disappearing layer:
(1) calls to skip procedures,
(2) calls to mover procedures, and
(3) calls that are annotated with `:mark`.

Data layering and control layering obviously interact, since the variables accessed by the control of a particular layer must indeed exist on that layer.

## Semantics

Civl considers two semantics for a concurrent program, the *preemptive* and the *non-preemptive* semantics.
The preemptive semantics is the standard interleaving semantics, where context switches can happen at any time between the execution of atomic actions.
This is the semantics that models the acutal behaviors of the concurrent program; the behaviors that we want to verify.
By contrast, the non-preemptive semantics allows a context switch only at the entry to or exit from a procedure
and at a call to a [yield invariant](#yield-invariants).
In particular, a context switch is not introduced just before or just after executing an atomic action.
The non-preemptive semantics simplifies reasoning, because fewer interleavings have to be considered.
Civl justifies going from the preemptive to the non-preemptive semantics using [mover types](#mover-types).

A program location where a context switch may happen is called a *yield location*.
Any execution path in a procedure from its entry to its exit is
partitioned into a sequence of execution fragments from one yield location to the next.
Each such execution fragment is called a *yield-to-yield fragment*.
Notice that these yield-to-yield fragments are dynamically scoped.
Yield locations specify the non-preemtive semantics.
Civl checks that there are "sufficiently many" yield locations such that reasoning about the non-preemtive semantics
is sufficient to reason about the preemptive semantics.

Going from preemtive to non-preemptive semantics simplifies the reasoning at one particular program layer.
In going from the layer-0 program to the layer-2 program, the set of yield locations progressively reduces because invocations of yielding procedures are replaced by invocations of atomic actions, thereby leading to simplified reasoning at the higher layer.


# Introducing and Hiding Variables

In a multi-layered refinement proof it is not only useful to change the granularity of atomicity, but also the state representation, i.e., the set of variables over which different program layers are expressed.
In this section, we describe how Civl supports introduction and hiding of both global and local variables.

In the following example program, the usage of variable `x` is changed into the usage of variable `y`.

```boogie
var {:layer 1,2} y:int;
var {:layer 0,1} x:int;

atomic action {:layer 2} atomic_read_y () returns (v:int)
{ v := y; }
yield procedure {:layer 1} read_y () returns (v:int)
refines atomic_read_y;
requires {:layer 1} x == y;
{
  call v := read_x();
}

atomic action {:layer 2} atomic_write_y (y':int)
modifies y;
{ y := y'; }
yield procedure {:layer 1}  write_y (y':int)
refines atomic_write_y;
{
  call write_x(y');
  call set_y_to_x();
}

action {:layer 1} set_y_to_x ()
modifies y;
{
  y := x;
}

atomic action {:layer 1} atomic_read_x () returns (v:int)
{ v := x; }
yield procedure {:layer 0} read_x () returns (v:int)
refines atomic_read_x;
{
  call v := intro_read_x();
}

atomic action {:layer 1} atomic_write_x (x':int)
modifies x;
{ x := x'; }
yield procedure {:layer 0} write_x (x':int)
refines atomic_write_x;
{
  call intro_write_x(x');
}

action {:layer 0} intro_read_x () returns (v:int)
{ v := x; }

action {:layer 0} intro_write_x (x':int)
modifies x;
{ x := x'; }
```

First, consider the layer ranges of `x` and `y`.
Variable `x` is introduced at layer 0 and hidden at layer 1, while `y` is introduced at layer 1 and hidden at layer 2.
Thus, they "overlap" at layer 1.
At layer 1 we have the atomic actions `atomic_read_x` and `atomic_write_x`,
which read from and write to `x`, respectively.
These actions are called by the yielding procedures `read_y` and `write_y`, respectively.
Now we want to show that `read_y` refines `atomic_read_y`, and `write_y` refines `atomic_write_y`.
Since `read_y` has the precondition `x == y` (the invariant that expresses our intended connection between `x` and `y`), we know that after reading `x` into the output variable `v`, also `v == y` holds, which is all we need to prove that `read_y` refines `atomic_read_y`.
In `write_y`, the input variable `y'` is written to `x` by `write_x`.
But what about `y`?
To express our intention for `y` we call the action `set_y_to_x`, which sets `y` to the current value of `x`, which at the time of invocation is `y'`.
Thus we get `y == y'` and we can prove that `write_y` refines `atomic_write_y`.

Actions like `set_y_to_x` have the specific purpose of assigning meaning to introduced variables.
As such, they are a kind of ghost code that does not cause a context switch;
recall that `atomic_write_x` and `set_y_to_x` need to execute without context switch to ensure `y == y'`.

We have the following layering constraints:

* If an action has a mover type, it can access any global variable that exists throughout the layer range of the action.
For example, `x` is introduced at layer 0 before `atomic_read_x` at layer 1, and is hidden at layer 1 together with `atomic_read_x`.
It is not permissible to introduce `atomic_read_x` at layer 0.
* If an action does not have a mover type, it can access any global variable whose layer range contains the layer range of the variable.
But the introduction layer of each modified variable must match the introduction layer of the action.
For example, `y` is introduced at layer 1 and thus can be modified by `set_y_to_x`.
Calls to such an action are treated as occurring only at the lower layer of the action.
This layer must be identical to either the disappearing layer of the caller or
the disappearing layer of each modified variable.

Variable introduction and hiding create the possibility of two different
programs at each layer, called the low program and the high program of the layer.
The high program at layer n contains all the code of the low program at n together with
calls to actions without mover types that introduce variables at layer n.
Neither the low nor the high program at layer n contains the variables hidden at n.
The variables introduced at layer n and the actions that introduce them
are present in the high program but not the low program at layer n.
Refinement checking at a layer is performed on the high program of that layer.

The [earlier example](#a-simple-layered-concurrent-program) only showed the high
program at each layer.
In that example, since the only layer at which variables are introduced is layer 0,
the low and high programs coincide at all layers except 0.
In the program described in this section, `x` is introduced at layer 0 and `y` is
introduced at layer 1.
Consequently, we have the following:

* The low program at layer 0 does not contain any variables;
the high program at layer 0 contains only `x`.
* The low program at layer 1 contains only `x`;
the high program at layer 1 contains both `x` and `y`.
* The low and high programs at layer 2 are identical and contain only `y`.

# Refinement Checking

We now explain how the specification `refines AtomicIncrBy2` is checked on the implementation of the procedure `IncrBy2`.
This refinement checking justifies the transformation of the layer-1 program to the layer-2 program.
Civl checks that along each execution path in `IncrBy2` from entry to exit, there is exactly one yield-to-yield fragment that behaves like `AtomicIncrBy2`.
(In this particular example, `IncrBy2` consists of only a single yield-to-yield fragment at layer 1.)
All other yield-to-yield fragments before and after this unique fragment leave state visible to the environment of `IncrBy2` unchanged.
The visible state for `IncrBy2` includes only the global variable `x`. In general, visible state for a procedure includes global variables and output variables of the procedure.

The signature of a procedure and its refined action must match unless a parameter of the procedure is annotated with `:hide` in
which case this parameter may be omitted from the signature of the refined action.
If a global variable is hidden at the disappearing layer of a procedure, then the visible state over which refinement is
checked does not include this variable.
Similary, any output parameter of the procedure annotated with `:hide` is excluded from the visible state.

If a yield procedure omits the refines clause, it is expected to refine the SKIP action.
This is tantamount to annotating each parameter of the procedure with `:hide`.
Since the SKIP action does not modify any variable, every yield-to-yield fragment in the procedure is allowed to modify
only those global variables that are hidden at the disappearing layer of the procedure.

A call marked by `:mark` attribute is treated specially during refinement checking.
Such a call must be to a callee procedure with the same disappearing layer as the caller.
It is expected that the refined action of the callee, when substituted at the call site, is the unique step
at which the caller's refined action appears to happen.

# Mover Types

In this section, we explain how Civl exploits commutativity of atomic actions to justify reasoning about non-preemptive semantics at each layer.
Civl allows each atomic action to be labeled by one of four mover types: `atomic`, `left`, `right`, and `both`.
The following code illustrates mover types for atomic actions.

```boogie
var {:layer 0,1} x:int;

yield invariant {:layer 1} yield_x(n: int);
invariant x >= n;

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

# Yield Invariants

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
invariant x >= n;

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

# Linear Typing and Permissions

Civl exploits linear typing to automatically inject logical assumptions when proving that a location or yield invariant is inteference-free or two actions commute with each other.

```boogie
type {:linear "X"} Tid;
var {:layer 0,1} a:[Tid]int;

yield procedure {:layer 0} Read({:linear "X"} tid: Tid, i: int) returns (val: int);
refines AtomicRead;
both action {:layer 1} AtomicRead({:linear "X"} tid: Tid, i: int) returns (val: int)
{
  val := a[tid];
}

yield procedure {:layer 0} Write({:linear "X"} tid: Tid, i: int, val: int);
refines AtomicWrite;
both action {:layer 1} AtomicWrite({:linear "X"} tid: Tid, i: int, val: int)
modifies a;
{
  a[tid] := val;
}

yield procedure {:layer 1} YieldInv({:linear "X"} tid: Tid, v: int);
requires a[tid] == v;
```

In the program above, the declaration of type `Tid` has the annotation `{:linear "X"}`.
This annotation indicates that values of type `Tid` are *permissions* that must be distributed among the variables of the program without duplication.
As the program executes, the permissions stored in the program variables may be redistributed but not duplicated, a condition that is verified by Civl.
These permissions are associated with a *domain* called `X`; disjointness is enforced within a domain but not across domains.
Different domains may use the same permission type.
For example, if `Tid` is the permission type for a domain `Y` also, then we would use the declaration `type {:linear "X", "Y"} Tid;`.

It is not required for all variables of type `Tid` to contain permissions.
To indicate that a variable contains permissions for domain `X`, it must have the annotation `{:linear "X"}`.
The parameter `tid` of atomic action `AtomicRead` contains permissions.
So does the parameter `tid` of `AtomicWrite`.
Consequently, if a thread is executing `AtomicRead(tid1, i1)` and another is executing `AtomicWrite(tid2, i2, val2)`, `tid1` and `tid2` must be distinct from each other.
This assumption is used to prove that `AtomicRead` and `AtomicWrite` are both movers.

Permissions are useful also for proving interference-freedom for location and yield invariants.
The yield invariant `YieldInv` is proved interference-free against any yield-to-yield code fragment that mutates `a` using `AtomicWrite`.

## Permission Collectors

In some programs, it is helpful to make a distinction between the value stored in a variable and the permission associated with it.
This increase in expressiveness is achieved by using a collector function from the type of the variable to the type of permissions.

```boogie
datatype {:linear "perm"} Perm { Left(i: int), Right(i: int) }

function {:inline}{:linear "perm"} IntCollector(i: int) : [Perm]bool
{
  MapConst(false)[Left(i) := true][Right(i) := true]
}
function {:inline}{:linear "perm"} IntSetCollector(iset: [int]bool) : [Perm]bool
{
  (lambda p: Perm :: is#Left(p) && iset[i#Left(p)])
}

var {:layer 0,1} barrierOn: bool;
var {:layer 0,1} barrierCounter: int;
var {:layer 0,1} {:linear "perm"} mutatorsInBarrier: [int]bool;

atomic action {:layer 1} AtomicEnterBarrier({:linear_in "perm"} i: int)
returns ({:linear "perm"} p: Perm)
modifies barrierCounter, mutatorsInBarrier;
{
    assert IsMutator(i);
    mutatorsInBarrier[i] := true;
    barrierCounter := barrierCounter - 1;
    p := Right(i);
}

atomic action {:layer 1} AtomicWaitForBarrierRelease(
  {:linear_in "perm"} p: Perm,
  {:linear_out "perm"} i: int)
modifies barrierCounter, mutatorsInBarrier;
{
    assert p == Right(i) && mutatorsInBarrier[i];
    assume !barrierOn;
    mutatorsInBarrier[i] := false;
    barrierCounter := barrierCounter + 1;
}
```

In the program above, the type `Perm` is a datatype with two constructors, `Left` and `Right`.
`Perm` is the permission type for domain `perm`.
The program variable that contain permissions in `Perm` are of type `int` and `[int]bool`.
The latter type represents a set of integers encoded as a map from `int` to `bool`; the set contains exactly those integers that are mapped to `true`.
The program defines two collectors, `IntCollector` and `IntSetCollector`.
The former collects permissions for a variable of type `int` and the latter collects permissions for a variable of type `[int]bool`.
The return type of each of these functions is `[Perm]bool`, representing a set of `Perm` values.
There are two implicitly-defined and auto-generated collector functions for each permission type.
These two collectors for the `Perm` type are shown below.

```boogie
function {:inline} PermCollector(x: Perm) : [Perm]bool {
  MapConst(false)[x := true]
}
function {:inline} PermSetCollector(xs: [Perm]bool) : [Perm]bool {
  xs
}
```

Permissions obtained by applying the collector function of the appropriate type to program variables continue to be distributed without being duplicated.
The enforced invariant states that permissions obtained from two distinct variables are disjoint.

## Permission Redistribution

A variable that is annotated with `{:linear "D"}` for any domain `D` is a linear variable.
Permissions are stored in a subset of the program's linear variables and may be redistributed among them as the program executes.
Civl performs a dataflow analysis to compute at each program location a set of available variables such that permissions in these variables are guaranteed to be disjoint.
The set of available variables at a program location contains every global linear variable but may contain only a subset of the local linear variables in scope.

Consider the atomic action `AtomicEnterBarrier` in the program above.
Input `i` of this action is annotated `{:linear_in "perm"}` indicating that the actual input variable corresponding to `i` at the call site must be available before the call and becomes unavailable after the call.
Output `p` is annotated `{:linear "perm"}` indicating that the actual output variable corresponding to `p` at the call site becomes available after the call.
The code of `AtomicEnterBarrier` redistributes the permissions stored in global variable `mutatorsInBarrier` and the input `i` among `mutatorsInBarrier` and output `p`.
Civl checks that this redistribution does not cause duplication.

The atomic action `AtomicWaitForBarrierRelease` has an input `i` annotated `{:linear_out "perm"}`.
This annotation indicates that the actual input variable corresponding to `i` at the call site will become available after the call.

Finally, the annotation `{:linear "perm"}` on an input parameter, although not used in the program above, would indicate that the
correspoding actual input variable at the call site must be available before the call and remains available after the call.

# Summarizing Asynchrony

In this section, we focus on Civl features for summarizing asynchronous procedure calls.

```boogie
yield procedure {:layer 1} Service()
{
  async call Callback();
}

yield procedure {:layer 0} Callback();
```

In the program above, the procedure `Service` makes an asynchronous call to the procedure `Callback`.
Both procedures `Callback` and `Service` refine the `SKIP` action.
At layer 1, the target of the asynchronous call to `Callback` in `Service` is rewritten to `SKIP`.
Since `SKIP` does not have any visible effect, the Civl refinement checker is able to show that `Service` refines `SKIP` despite the asynchronous call in its implementation.

Next, we show how to synchronize an asynchronous call to an atomic action with visible side effects.

```boogie
var {:layer 0,2} x:int;

yield procedure {:layer 1} Service()
refines A_Inc;
{
  async call {:sync} Callback();
}

both action {:layer 1,2} A_Inc()
modifies x;
{ x := x + 1; }
yield procedure {:layer 0} Callback();
refines A_Inc;
```

In the program above, the procedure `Service` makes an asynchronous call to the procedure `Callback`, similar to the first program shown in this section.
The difference in this example is that both `Service` and `Callback` refine the atomic action `A_Inc` that increments a global variable `x`.
Since `A_Inc` is a left mover (in fact, a both mover) it is possible to execute it exactly at the point of its asynchronous invocation.
This intention is indicated by the `:sync` annotation on the asynchronous call.

## Pending asyncs

As described in the last section, Civl allows a procedure to make an asynchronous procedure call.
Additionally and symmetrically, Civl also allows an atomic action to make an asynchronous call to an atomic action.
Such a call is called a pending async, for brevity, to indicate that the effect of the asynchronous call is pending and becomes visible only once the side effects of the caller atomic action have been applied.

Pending asyncs increase the expressiveness of refinement in Civl.
Without pending asyncs, summarizing the effect of a procedure that makes an asynchronous procedure call required synchronization of the call.
With pending asyncs, it is possible to achieve this summarization via a pending async in the refined action.
Civl also allows a pending async in an atomic action to be eliminated subsequently.
The next example illustrates the Civl features that allow the user to create and eliminate pending asyncs.

```boogie
var {:layer 0,3} x:int;

yield procedure {:layer 2} Client()
refines A_Inc;
{
  call Service();
}

atomic action {:layer 1} A_Service()
creates A_Inc;
refines A_Inc;
{
  call create_async(A_Inc());
}
yield procedure {:layer 0} Service()
refines A_Service;
{
  async call Callback();
}

async both action {:layer 1,3} A_Inc()
modifies x;
{ x := x + 1; }
yield procedure {:layer 0} Callback();
refines A_Inc;
```

The call to `Callback` in procedure `Service` is not annotated with `:sync`.
Therefore, Civl infers that this call must be converted into a pending async to `A_Inc` in the refined action `A_Service`.
The action `A_Inc` is qualified with the declaration `async` to indicate that it may be used as a pending async.
An async action is not allowed to have any output parameters.
A datatype declaration corresponding to the signature of such an action is automatically created by Civl.
A value of this datatype may be used as parameter to the primitive `create_async` in atomic action specifications
to create a pending async.
The `creates` specification contains the name of each atomic action that may be created as a pending async.
The atomic action `A_Service` creates a single pending async `A_Inc()`.

To complete the round trip, the pending async in the action `A_Service` is eliminated to get back the atomic action `A_Inc`.
This elimination is indicated by the `refines A_Inc` specification on `A_Service`.
Since `A_Inc` is a left mover, the verifier may pretend that the asynchronous call can be executed synchronously.

Finally, the procedure `Client` which itself calls `Service` is shown to refine `A_Inc` also.
The target of this call is rewritten to `A_Service` at layer 1 and to `A_Inc` at layer 2.

## Inductive sequentialization

In the last example, we saw how to eliminate a single pending async from an action.
Civl also provides a feature to eliminate unboundedly many pending asyncs from an action.
We now show this technique, known as inductive sequentialization, using an example.

```boogie
var {:layer 0,2} x:int;

both action {:layer 2} A_Add (n: int)
modifies x;
{ assert 0 <= n; x := x + n; }

action {:layer 1} INV(n: int)
creates A_Inc;
modifies x;
{
  var {:pool "A"} i: int;
  assert 0 <= n;
  assume {:add_to_pool "A", i} {:add_to_pool "A", i+1} 0 <= i && i <= n;
  x := x + i;
  call create_multi_asyncs(MapConst(0)[A_Inc() := n - i]);
}

atomic action {:layer 1} Async_Add(n: int)
refines A_Add using INV;
creates A_Inc;
{
  assert 0 <= n;
  assume {:add_to_pool "A", 0} true;
  call create_multi_asyncs(MapConst(0)[A_Inc() := n]);
}

async both action {:layer 1,2} A_Inc ()
modifies x;
{ x := x + 1; }
```

The action `Async_Add` uses the primitive `create_multi_asyncs` to create `n` pending asyncs
of action `A_Inc` each of which asynchronously increments the global variable `x` by 1.
As before, the action `A_Inc` is a left mover.
We would like to use the mover type of `A_Inc` to show that `Async_Add` refines an action
`A_Add` that increments `x` by `n` in one atomic step.

To do this proof we use an auxiliary invariant `INV` and indicate it should be used for the
refinement proof in the refines specification for `Async_Add`.
The action `INV` is a generalization of `Async_Add`.
`INV` includes every behavior of `Async_Add` and is also closed under extension by the eliminated action `A_Inc`.
It is important to understand how `INV` is specified.
The local variable `i` is initialized nondeterministically and constrained to be between `0` and `n`, both inclusive.
The nondeterministic initialization choice represents the number of pending asyncs that have already executed,
as indicated by the increment of `x` by `i`.
Finally, the remaining `n-i` pending asyncs of `A_Inc` are created to indicate those pending asyncs that remain to
be executed.
