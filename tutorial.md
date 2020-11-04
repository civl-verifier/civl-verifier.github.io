---
title: Tutorial
---

# Overview
- Civl is an extension of Boogie
- structure of Civl file (yielding procedures, atomic actions, yield invariants)


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

# Refinement layers
- basic mechanics
- abstraction and reduction are symbiotic

# Tackling asynchony
- Summarizing asynchronous calls using pending asyncs
- Eliminating pending asyncs
