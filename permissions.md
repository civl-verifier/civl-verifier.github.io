---
title: Permissions 
nav_order: 7
---

Civl provides a polymorphic type `One T` to store permissions.

```boogie
datatype One<T> { One(val: T) }
```

Global variables and procedure parameters of type `One _` are indicated to be linear by annotating with the attribute `{:linear}`.
A linear variable `x` of type `One T` contains the singleton set of permissions `{x}`.
The type `One T` may be nested in datatypes.

```boogie
datatype A<T> { A(v: One T, u: int) }
```

A linear variable `x` of type `A T` contains the singleton set of permissions `{x->v}`.
A linear variable `x` of type `Set (One T)` contains the set of permissions `x`.
A linear variable `x` of type `Map K V` contains the union of permissions inside `x->val[k]`
for each `k` in `x->dom`.
Additionally, if `K = One _` then the set `x->dom` is added to the set of permissions in `x`.

The permissions stored in linear variables are guaranteed to disjoint from each other in any reachable
state of the program.
As the program executes, the permissions stored in the program variables may be redistributed but not duplicated,
a condition that is verified via linear typing implemented in the Civl type checker.
Civl exploits this disjointness invariant to automatically inject logical assumptions when proving that a 
location or yield invariant is interference-free or two actions commute with each other.


```boogie
type Tid;
var {:layer 0,1} a: [Tid]int;

yield procedure {:layer 0} Read({:linear} tid: One Tid) returns (v: int);
refines AtomicRead;
both action {:layer 1} AtomicRead({:linear} tid: One Tid) returns (v: int)
{
  v := a[tid->val];
}

yield procedure {:layer 0} Write({:linear} tid: One Tid, v: int);
refines AtomicWrite;
both action {:layer 1} AtomicWrite({:linear} tid: One Tid, v: int)
modifies a;
{
  a[tid->val] := v;
}

yield procedure {:layer 1} YieldInv({:linear} tid: One Tid, v: int);
requires a[tid->val] == v;
```

In the program above,
if a thread is executing `AtomicRead(tid1, i1)` and another is executing `AtomicWrite(tid2, i2, val2)`, `tid1` and `tid2` must be distinct from each other.
This assumption is used to prove that `AtomicRead` and `AtomicWrite` are both movers.
Permissions are useful also for proving interference-freedom for yield invariants.
The yield invariant `YieldInv` is proved interference-free against any yield-to-yield code fragment that mutates `a` using `AtomicWrite`.

## Permission Redistribution

```boogie
datatype Perm { Left(i: int), Right(i: int) }

datatype Tid { Tid(i: int, ps: Set (One Perm)) }

var {:layer 0,1} barrierOn: bool;
var {:layer 0,1} barrierCounter: int;
var {:layer 0,1} {:linear} mutatorsInBarrier: Set (One Perm);

atomic action {:layer 1} AtomicEnterBarrier({:linear_in} tid: Tid) returns ({:linear} tid': Tid)
{
  var p: One Perm;
  var i: int;

  i := tid->i;
  assert IsMutator(i);
  tid' := tid;
  p := One(Left(i));
  call One_Get(tid'->ps, p);
  call One_Put(mutatorsInBarrier, p);
  barrierCounter := barrierCounter - 1;
}

atomic action {:layer 1} AtomicWaitForBarrierRelease({:linear_in} tid: Tid) returns ({:linear} tid': Tid)
{
  var p: One Perm;
  var i: int;

  i := tid->i;
  assert Set_Contains(tid->ps, One(Right(i)));
  assert Set_Contains(mutatorsInBarrier, One(Left(i)));
  assume !barrierOn;
  p := One(Left(i));
  call One_Get(mutatorsInBarrier, p);
  tid' := tid;
  call One_Put(tid'->ps, p);
  barrierCounter := barrierCounter + 1;
}
```

Civl performs a dataflow analysis to compute at each program location a set of available variables such that permissions in these variables are guaranteed to be disjoint.
The set of available variables at a program location contains every global linear variable but may contain only a subset of the local linear variables in scope.

Consider the atomic action `AtomicEnterBarrier` in the program above.
Input `tid` of this action is annotated `{:linear_in}` indicating that the actual input variable corresponding to `i`
at the call site must be available before the call and becomes unavailable after the call.
Output `tid'` is annotated `{:linear}` indicating that the actual output variable corresponding to `p`
at the call site becomes available after the call.
The code of `AtomicEnterBarrier` redistributes the permissions stored in global variable `mutatorsInBarrier`
and the input `tid` among `mutatorsInBarrier` and output `tid'`.
Civl checks that this redistribution does not cause duplication.

The atomic action `AtomicWaitForBarrierRelease` has an interface similar to `AtomicEnterBarrier`.
This action also redistributes the permissions stored in global variable `mutatorsInBarrier`
and the input `tid` among `mutatorsInBarrier` and output `tid'`.

Although not used in the program above, input parameters may be annotated with `{:linear}` and `{:linear_out}`.
The annotation `{:linear}` on an input parameter indicates that the
corresponding actual input variable at the call site must be available before the call and remains available after the call.
The annotation `{:linear_out}` indicates that the actual input variable corresponding to at the call site will become available after the call.