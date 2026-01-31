---
title: Syntax
nav_order: 1
---

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
var {:layer 0,10} x: int;
```

Global variable `x` is *introduced* at layer `0` and *hidden* at layer `10`. We
call `0` the *introduction/lower layer* of `x`, and `10` the *disappearing/upper
layer* of `x`.
The layer range `{:layer n}` on a global variable is identical to `{:layer n,n}`.
If a layer range is not provided, the variable gets the default layer range of [0,∞].

## Actions

*Atomic actions* are the building blocks of a Civl program, encapsulating all
accesses to global variables.

An atomic action typically has a *mover type* and a *layer range*.
The mover type is
either `atomic` (non-mover), `right` (right mover), `left` (left mover), or
`both` (both mover).
It is possible to declare an atomic action without a mover type,
in which case the default mover type `atomic` is assigned to the action.

```boogie
atomic action {:layer 2,5} FOO (i: int) returns (j: int)
modifies x; // optional
{
  assert x > 0;
  j := x;
  x := x + i;
  assert x >= j;
}
```

Atomic action `FOO` is *available* from layer `2` up to layer `5` (*introduced*
at layer `2` and *disappearing* at layer `5`). The gate of `FOO` is `x > 0`, and the
transition relation states that output parameter `j` returns the current value
of global variable `x`, and the value of input parameter `i` is added to `x`.
The layer range `{:layer n}` on an action is identical to `{:layer n,n}`.

The body of an atomic action must not have loops.
Actions may call other actions as long as the call graph is acyclic
and for each call the caller's layer range is contained in the callee's layer range.

An atomic action may fail if it executes an assert statement whose condition does not hold.
Optionally, an atomic action may be annotated with one or more ```asserts``` clause,
which allows the user to safely lift all failure conditions to the beginning of the action.

```boogie
atomic action {:layer 2,5} FOO (i: int) returns (j: int)
asserts x > 0;
asserts i >= 0;
{
  assert x > 0;
  j := x;
  x := x + i;
  assert x >= j;
}
```

## Yield Invariants

A *yield invariant* has a layer number and a sequence of `preserves` clauses (but
no body).

```boogie
yield invariant {:layer 1} yield_x(i: int);
preserves i <= x;
```

Yield invariant `yield_x` states that global variable `x` is greater than or
equal to parameter `i`.
This invariant is applicable to reasoning only at layer `1`.

## Yielding Procedures

Yielding procedures describe the actual concurrent program.
There are two kinds: *action procedures* that get summarized
by atomic actions, and *mover procedures* that get summarized by
pre/postconditions.

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

A mover procedure has a *disappearing layer* and a *mover type*.

```boogie
yield right procedure {:layer 1} foo (...) returns (...);
```

The local variables of a yielding procedure have a layer range.

```boogie
yield procedure {:layer 5} Foo({:layer 2,4} x: int) returns ({:layer 3} y: int)
{
  var {:layer 2,3} z: int;
  ...
}
```

Suppose the yielding procedure has the disappearing layer N.
The layer range of each local variable of this procedure is
required to be a subset of the layer range [0,N].
The layer range `{:layer n}` on a local variable is identical to `{:layer n,n}`.
If a layer range is not provided, the variable gets the default layer range of [0,N].

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

## Parameters

Every input and output parameter of a yielding procedure has a layer range.
Implicitly, it ranges from the lowest layer up to the disappearing layer of the
procedure. A different layer range can be assigned to every parameter using the
`:layer` attribute.

Parameters of action procedures can be annotated with `:hide` to declare that
the parameter does not occur in the refined atomic action.

## Pure Actions

A pure action does not read or modify global variables,
is layer independent, and has the mover type `both`.

```boogie
pure action Add(a: int, b: int) returns (c: int)
{ c := a + b; }
```

A pure action serve two purposes.
First, a pure action can factor out computation that may be reused
via calls from other actions.
The layer independent nature of pure actions increases this reusability.

Second, a pure action may be called from a yield procedure to add computation
that introduces local or global variables at a layer.
Such a call must be annotated to indicate the layer at which the new variables
are being introduced.

```boogie
call {:layer 3} x := Add(y, z);
```

The call above introduces a variable `x` at layer 3;
the variables `y` and `z` are expected to exist at layer 3 as well.

## Pure Procedures

A pure procedure does not read or modify global variables and is expected to
terminate for all inputs.

```boogie
pure procedure ToSet(a: Vec int) returns (b: Set int)
ensures (forall i: int :: 0 <= i && i < Vec_Len(a) ==> Set_Contains(Vec_Nth(a, i)));
{ ... }

pure procedure Lemma_add_to_set (x: X, set: [X]bool);
requires !set[x];
ensures card(set[x := true]) == card(set) + 1;
```

Similar to pure actions, a pure procedure may be called at a particular layer 
from a yield procedure to introduce new variables at that layer.
Additionally, these procedures support the injection of lemmas and proof hints.
In particular, this is a useful alternative to global quantified axioms.
For example, the pure procedure `Lemma_add_to_set` states the fact about set cardinality,
that adding an element to a set increases the sets cardinality by one.