---
title: Tutorial
---

# Overview

CIVL is an extension of Boogie. In Boogie, (almost every) abstract syntax tree
node can be annotated with attributes of the form `{:attr e1, e2, ...}`, where
`attr` is the attribute name and `e1, e2, ...` are expressions (denoting
parameters of the attribute). CIVL programs are embedded in Boogie using
attributes. This section provides a brief overview of CIVL's constructs and how
they are expressed using attributes.

## Types, Functions, Constants

Types, functions, and constants are declared just as in Boogie.

## Global / Shared Variables

Global variables have a *layer range*.

```
var {:layer 0,10} x:int;
```

Global variable `x` is *introduced* at layer `0` and *hidden* at layer `10`. We
call `0` the *introduction/lower layer* of `x`, and `10` the *disappearing/upper
layer* of `x`.

## Actions

*Atomic actions* are the building blocks of a CIVL program, encapsulating all
accesses to global variables. *Introduction actions* are a particular kind of
action used to give meaning to introduced variables.

### Atomic Actions

An atomic actions has a *mover type* and a *layer range*. The mover type is
either `:atomic` (non-mover), `:right` (right mover), `:left` (left mover), or
`:both` (both mover). The body of an atomic action consists of a sequence of
assert commands, called the *gate*, followed by a loop-free call-free block of
code, denoting a *transition relation*.

```
procedure {:atomic}{:layer 2,5} FOO (i: int) returns (j: int)
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

Atomic actions support *backward assignments*.

```
p  := {:backward} x;
```

### Introduction Actions

An introduction action has a single *layer number* (and no mover type).

```
procedure {:intro}{:layer 2} BAR (...) returns (...)
{
  ...
}
```

## Yield Invariants

A *yield invariant* has a layer number and a sequence of `requires` clauses (but
no body).

```
procedure {:yield_invariant}{:layer 1} yield_x(i: int);
requires i <= x;
```

Yield invariant `yield_x` states that global variable `x` is greater than or
equal to parameter `i`.

## Yielding Procedures

Yielding procedures (identified by the `:yields` attribute) describe the actual
concurrent program. There are two kinds: *action procedures* that get summarized
by atomic actions, and *mover procedures* that get summarized by
pre/postconditions.

### Action Procedure

An action procedure has a *disappearing layer* and a *refined atomic action*.
The `modifies` clause is implicit and contains all global variables.

```
procedure {:yields}{:layer 1}{:refines "FOO"} foo (...) returns (...);
```

Action procedure `foo` *disappears* at layer `1` and *refines* the atomic action
`FOO`.

If no `:refines` attribute is given, then the procedure refines the implicitly
declared atomic action `SKIP`.

```
procedure {:both}{:layer 0,∞} SKIP () { }
```

### Mover Procedure

A mover procedure has a *disappearing layer* and a *mover type*. The `modifies`
clause has to be provided.

```
procedure {:yields}{:layer 1}{:right} foo (...) returns (...);
modifies ...;
```

### Implementations

The implementations (i.e., bodies) of yielding procedures support the following
additional commands.

* **Parallel call**: `par i := A(j) | k := B(l)`
* **Asynchronous call**: `async call A(i)`
* **Yield point**: `yield`

### Specifications

Every precondition, postcondition, assertion, and loop invariant is annotated
with a sequence of layer numbers (`{:layer l1, l2, ...}`).

Yield invariants can be invoked in calls, parallel calls, as preconditions
(`:yield_requires`), postconditions (`:yield_requires`), and loop invariants
(`:yield_loop`).

### Parameters

Every input and output parameter of a yielding procedure has a layer range.
Implicitly, it ranges from the lowest layer up to the disappearing layer of the
procedure. A different layer range can be assigned to every parameter using the
`:layer` attribute.

Parameters of action procedures can be annotated with `:hide` to declare that
the parameter does not occur in the refined atomic action.

### Refinement

A call can be annotated with `:refines`.

Every loop is either *non-yielding* or *yielding* (denoted with `:yields` on a
loop invariant).

Loops might be annotated with `:terminates`.

## Lemma Procedures

Lemma procedures support the injection of (unverified) facts and proof hints. In
particular, this is a useful alternative to global quantified axioms.

```
procedure {:lemma} Lemma_add_to_set (x: X, set: [X]bool);
requires !set[x];
ensures card(set[x := true]) == card(set) + 1;
```

The lemma procedure `Lemma_add_to_set` states the fact about set cardinality,
that adding an element to a set increases the sets cardinality by one.

# Layered concurrent programs

CIVL verifies a layered concurrent program by verifying each layer separately.
We show an example to explain how a layered program represents a sequence of increasingly simpler concurrent programs.
Understanding this foundational aspect of CIVL will make it easier to understand everything explained later.
```
var {:layer 0,2} x: int;

procedure {:yields} {:layer 0} {:refines "AtomicIncr"} Incr();
procedure {:left} {:layer 1} AtomicIncr()
modifies x;
{ x := x + 1; }

procedure {:yields} {:layer 1} {:refines "AtomicIncrBy2"} IncrBy2()
{
  par Incr() | Incr();
}
procedure {:layer 2} {:atomic} AtomicIncrBy2()
modifies x;
{ x := x + 2; }

procedure {:yields} {:layer 2} Main()
{
  call IncrBy2();
}
```
The program above represents three concurrent programs, at layers 0, 1, and 2, that share parts of their code.
Layer 0 is the most concrete and layer 1 is the most abstract.
The annotation `{:layer 0,2}` on global variable `x` is a range of layers from 0 to 2 indicating that `x` exists at all layers in this layer range.
The annotation `{:layer 0}` on `Incr` indicates that 0 is the highest layer on which `Incr` exists.
The annotation `{:refines "AtomicIncr"}` on `Incr` indicates that on layers greater than 0 a call to Incr is rewritten to a call to `AtomicIncr`.
Similarly, procedure `IncrBy2` exists on layers 1 and lower and is replaced by `AtomicIncrBy` at layers above 1.
```
// Program at layer 0

var x: int;

procedure {:yields} Incr();

procedure {:yields} IncrBy2()
{
  par Incr() | Incr();
}

procedure {:yields} Main()
{
  call IncrBy2();
}
```
The layer-0 program, shown above, contains only procedures and no atomic actions.
The implementation of procedure `Incr` is not provided but it is known from the description of the layered program, specifically `{:refines "AtomicIncr"}` annotation on `Incr`, that this implementation behaves like the atomic action `AtomicIncr`.
```
// Program at layer 1

var x: int;

procedure AtomicIncr()
modifies x;
{ x := x + 1; }

procedure {:yields} IncrBy2()
{
  call AtomicIncr();
  call AtomicIncr();
}

procedure {:yields} Main()
{
  call IncrBy2();
}
```
In the layer-1 program, shown above, the parallel call to `Incr` is rewritten to a sequence of calls to `AtomicIncr`.
The justification for this rewrite is that `Incr` refines `AtomicIncr` and `AtomicIncr` is a left mover.
```
// Program at layer 2

var x: int;

procedure AtomicIncrBy2()
modifies x;
{ x := x + 2; }

procedure {:yields} Main()
{
  call AtomicIncrBy2();
}
```
In the layer-2 program, shown above, the call to procedure `IncrBy2` in `Main` is rewritten to a call to atomic action `AtomicIncrBy2`.
The justification for this rewrite is that `IncrBy2` refines `AtomicIncrBy2`.

In CIVL's model of the semantics of a concurrent program, a context switch is allowed only at entry or exit from a procedure or at an explicit `yield` statement.
In particular, a context switch is not introduced just before or just after executing an atomic action.
In going from the layer-0 program to the layer-2 program, the set of program locations where context switches may happen progressively reduces, thereby leading to simplified reasoning at the higher layer.

# Tackling interference

Reasoning about concurrent programs is difficult because of the
possibility of interference among concurrently-executing procedures.
We now present the various features in CIVL targeted towards specifying
and controlling interference.
The following program introduces location invariants,
the simplest specification idiom addressing interference.
```
var {:layer 0,1} x:int;

procedure {:yields} {:layer 1} p()
requires {:layer 1} x >= 5;
ensures  {:layer 1} x >= 8;
{
  call Incr(1);
  yield; assert {:layer 1} x >= 6;
  call Incr(1);
  yield; assert {:layer 1} x >= 7;
  call Incr(1);
}

procedure {:yields} {:layer 1} q()
{
  call Incr(3);
}

procedure {:atomic} {:layer 1} AtomicIncr(val: int)
modifies x;
{
  x := x + val;
}

procedure {:yields} {:layer 0} {:refines "AtomicIncr"} Incr(val: int);
```
The program above has two yielding procedures, `p` and `q`, each
accessing the shared variable `x`.
Accesses to `x` are encapsulated in the atomic action `AtomicIncr`,
which increments `x` by the amount supplied in the parameter `val`.
`AtomicIncr` is refined by the procedure `Incr`, whose implementation
is not provided.
The `yield` statement indicates that the executing thread may be suspended to allow another concurrently-executing thread to run.
A `yield` statement may be optionally followed by a sequence of assert statements that collectively form the location invariant for the location of the yield statement.
The `requires` annotations provide the location invariant for the implicit yield at procedure entry.
Similarly, the `ensures` annotations provide the location invariant for the implicit yield at procedure exit.

Each location invariant in the program above has a layer annotation `{:layer 1}`.
This annotation indicates that the location invariant is applicable to the concurrent program at layer 1.
To allow for the same location invariant to be reused across different layers, CIVL allows the layer annotation on a location invariant to have a list of layers, e.g. `{:layer 1,3,5}`.
The verification goal in the program above is to establish that all location invariants at layer 0 hold.

CIVL checks that a location invariant at a yield is established by the thread when control arrives at the yield.
CIVL also checks that each location invariant is preserved by any yield-to-yield code fragment in any procedure.
Together, these checks guarantee that it is safe to assume the location invariant when the thread resumes execution after the yield statement.
All specifications in the program above are verified.

The next code snippet shows how to rewrite procedure `p` using yield invariants.
It also introduces `yield_preserves` and `yield_loop`.

```
procedure {:yield_invariant} {:layer 1} yield_x(n: int);
requires x >= n;

procedure {:yields} {:layer 1}
{:yield_requires "yield_x", old(x)}
{:yield_ensures "yield_x", old(x)+3}
p()
{
  call Incr(1);
  call yield_x(x);
  call Incr(1);
  call yield_x(x);
  call Incr(1);
}

procedure {:yields} {:layer 1}
{:yield_preserves "yield_x", old(x)}
q()
{
  while (*)
  {:yield_loop "yield_x", old(x)}
  {
    call Incr(3);
  }
}
```

The next code snippet explains movers.

```
procedure {:yields} {:layer 1}
{:yield_requires "yield_x", 5}
{:yield_ensures "yield_x", 8}
p()
{
  call Incr(1);
  call Incr(1);
  call Incr(1);
}

procedure {:both} {:layer 1,1} AtomicIncr(val: int)
modifies x;
{
  x := x + val;
}
```

The next code snippet explains permissions by explaining their use in
proving mover types for `AtomicRead` and `AtomicWrite`.

```
type {:linear "tid"} Tid;
var {:layer 0,1} a:[Tid]int;

procedure {:yields} {:layer 1}
Incr({:linear "tid"} tid: int)
{
  var t:int;

  call t := Read(tid, i);
  call Write(tid, i, t + 1);
}

procedure {:both} {:layer 1,1}
AtomicRead({:linear "tid"} tid: int, i: int) returns (val: int)
{
  val := a[tid];
}

procedure {:yields} {:layer 0} {:refines "AtomicRead"}
Read({:linear "tid"} tid: int, i: int) returns (val: int);

procedure {:both} {:layer 1,1}
AtomicWrite({:linear "tid"} tid: int, i: int, val: int)
modifies a;
{
  a[tid] := val;
}

procedure {:yields} {:layer 0} {:refines "AtomicWrite"}
Write({:linear "tid"} tid: int, i: int, val: int);
```

Explain that there is a general and customizable notion of collector functions.
The next code snippet explains collectors.

```
type {:linear "perm"} {:datatype} Perm;
function {:constructor} Left(i: int): Perm;
function {:constructor} Right(i: int): Perm;

function {:inline} {:linear "perm"} IntCollector(i: int) : [Perm]bool
{
  MapConst(false)[Left(i) := true][Right(i) := true]
}
function {:inline} {:linear "perm"} IntSetCollector(iset: [int]bool) : [Perm]bool
{
  (lambda p: Perm :: is#Left(p) && iset[i#Left(p)])
}

var {:layer 0,1} barrierOn: bool;
var {:layer 0,1} barrierCounter: int;
var {:layer 0,1} {:linear "perm"} mutatorsInBarrier: [int]bool;

procedure {:atomic} {:layer 1} AtomicEnterBarrier({:linear_in "perm"} i: int) returns ({:linear "perm"} p: Perm)
modifies barrierCounter, mutatorsInBarrier;
{
    assert IsMutator(i);
    mutatorsInBarrier[i] := true;
    barrierCounter := barrierCounter - 1;
    p := Right(i);
}

procedure {:atomic} {:layer 1} AtomicWaitForBarrierRelease({:linear_in "perm"} p: Perm, {:linear_out "perm"} i: int)
modifies barrierCounter, mutatorsInBarrier;
{
    assert p == Right(i) && mutatorsInBarrier[i];
    assume !barrierOn;
    mutatorsInBarrier[i] := false;
    barrierCounter := barrierCounter + 1;
}
```

# Abstraction and reduction are symbiotic

The next code snippet explains that abstraction can lead to a more precise mover type.

```
type {:linear "tid"} X;

var {:layer 0,2} x: int;

procedure {:yields} {:layer 0} {:refines "AtomicIncr"} Incr();

procedure {:atomic} {:layer 1,2} AtomicIncr()
modifies x;
{ x := x + 1; }

procedure {:yields} {:layer 0} {:refines "AtomicRead"} Read() returns (v: int);

procedure {:atomic} {:layer 1} AtomicRead() returns (v: int)
{ v := x; }

procedure {:yields} {:layer 1} {:refines "AbstractAtomicRead"} _Read() returns (v: int)
{
  call Read();
}

procedure {:left} {:layer 2} AbstractAtomicRead() returns (v: int)
{ assume v <= x; }
```

# Tackling asynchony

The next code snippet shows how to summarizing asynchronous calls directly without using pending asyncs.

```
var {:layer 0,2} x : int;

procedure {:yields} {:layer 1} {:refines "atomic_inc_x"} main (n: int)
requires {:layer 1} n >= 0;
{
  call inc(n);
}

procedure {:yields} {:left} {:layer 1} {:terminates}  inc (i : int)
modifies x;
requires {:layer 1} i >= 0;
ensures {:layer 1} x == old(x) + i;
{
  if (i > 0)
  {
    call inc_x(1);
    async call {:sync} inc(i-1);
  }
}

procedure {:both} {:layer 1,2} atomic_inc_x (n: int)
modifies x;
{ x := x + n; }

procedure {:yields} {:layer 0} {:refines "atomic_inc_x"} inc_x (n: int);
```

* Summarizing asynchronous calls using pending asyncs
* Eliminating pending asyncs
