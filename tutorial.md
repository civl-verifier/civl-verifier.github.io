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

A *yield invariant* has a layer number and a sequence of `ensures` clauses (but
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

# Tackling noninterference

The following program explains location invariants.
In order to reduce mystery, there is brief explanation of layer annotations also.

```
var {:layer 0,1} x:int;

procedure {:yields} {:layer 1} p()
requires {:layer 1} x >= 5;
ensures  {:layer 1} x >= 8;
{
  call Incr(1);
  yield;
  assert {:layer 1} x >= 6;
  call Incr(1);
  yield;
  assert {:layer 1} x >= 7;
  call Incr(1);
}

procedure {:yields} {:layer 1} q()
{
  call Incr(3);
}

procedure {:atomic} {:layer 1,1} AtomicIncr(val: int)
modifies x;
{
  x := x + val;
}

procedure {:yields} {:layer 0} {:refines "AtomicIncr"} Incr(val: int);
```

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

# Refinement layers

The next code snippet explains the basic mechanics.

```
type {:linear "tid"} X;

var {:layer 0,2} x: int;

procedure {:yields} {:layer 0} {:refines "AtomicIncr"} Incr();

procedure {:left} {:layer 1} AtomicIncr()
modifies x;
{ x := x + 1; }

procedure {:yields} {:layer 1} {:refines "AtomicIncrBy2"} IncrBy2()
{
  par Incr() | Incr();
}

procedure {:left} {:layer 2} AtomicIncrBy2()
modifies x;
{ x := x + 2; }

procedure {:yields} {:layer 2} Main({:linear "tid"} tid: X)
{
  call IncrBy2();
}
```

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
