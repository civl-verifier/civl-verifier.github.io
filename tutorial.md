---
title: Tutorial
---

This tutorial is work in progress.

# Structure of CIVL Programs

...

# Lock Example

```
type Tid;
type {:datatype} OptionTid;
function {:constructor} None(): OptionTid;
function {:constructor} Some(tid: Tid): OptionTid;

var {:layer 0, 1} b: bool;
var {:layer 0, 3} count: int;
var {:layer 1, 2} l: OptionTid;

////////////////////////////////////////////////////////////////////////////////

procedure {:yield_invariant} {:layer 1} LockInv();
requires b <==> (l != None());

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic} {:layer 3,3} IncrSpec()
modifies count;
{
    count := count + 1;
}
procedure {:yields} {:layer 2} {:refines "IncrSpec"}
{:yield_requires "LockInv"}
{:yield_ensures  "LockInv"}
Incr({:layer 1,2} {:hide} {:linear "tid"} tid: Tid)
{
    var t: int;

    call Acquire(tid);
    par t := LockedRead(tid) | LockInv();
    par LockedWrite(tid, t+1) | LockInv();
    call Release(tid);
}

////////////////////////////////////////////////////////////////////////////////

procedure {:right} {:layer 2,2} atomic_Acquire({:linear "tid"} tid: Tid)
modifies l;
{
    assume l == None();
    l := Some(tid);
}
procedure {:yields} {:layer 1} {:refines "atomic_Acquire"}
{:yield_requires "LockInv"}
{:yield_ensures  "LockInv"}
Acquire({:layer 1} {:linear "tid"} tid: Tid)
{
    var t: bool;

    while (true)
    invariant {:layer 1}{:yields}{:yield_loop "LockInv"} true;
    {
      call t := CAS(false, true);
      if (t) {
        call set_l(Some(tid));
        break;
      }
    }
}

procedure {:left} {:layer 2,2} atomic_Release({:linear "tid"} tid: Tid)
modifies l;
{
    assert l == Some(tid);
    l := None();
}
procedure {:yields} {:layer 1} {:refines "atomic_Release"}
{:yield_requires "LockInv"}
{:yield_ensures  "LockInv"}
Release({:layer 1} {:linear "tid"} tid: Tid)
{
    var t: bool;

    call t := CAS(true, false);
    call set_l(None());
}

procedure {:both} {:layer 2,2} atomic_LockedRead({:linear "tid"} tid: Tid) returns (v: int)
{
    assert l == Some(tid);
    v := count;
}
procedure {:yields} {:layer 1} {:refines "atomic_LockedRead"} LockedRead({:layer 1} {:linear "tid"} tid: Tid) returns (v: int)
{
    call v := Read();
}

procedure {:both} {:layer 2,2} atomic_LockedWrite({:linear "tid"} tid: Tid, v: int)
modifies count;
{
    assert l == Some(tid);
    count := v;
}
procedure {:yields} {:layer 1} {:refines "atomic_LockedWrite"} LockedWrite({:layer 1} {:linear "tid"} tid: Tid, v: int)
{
    call Write(v);
}

////////////////////////////////////////////////////////////////////////////////

procedure {:atomic} {:layer 1,1} atomic_Read() returns (v: int)
{
    v := count;
}

procedure {:atomic} {:layer 1,1} atomic_Write(v: int)
modifies count;
{
    count := v;
}

procedure {:atomic} {:layer 1,1} atomic_CAS(old_b: bool, new_b: bool) returns (success: bool)
modifies b;
{
    success := b == old_b;
    if (success) {
        b := new_b;
    }
}

procedure {:inline} {:intro} {:layer 1} set_l(v: OptionTid)
modifies l;
{
    l := v;
}

procedure {:yields} {:layer 0} {:refines "atomic_Read"} Read() returns (v: int);
procedure {:yields} {:layer 0} {:refines "atomic_Write"} Write(v: int);
procedure {:yields} {:layer 0} {:refines "atomic_CAS"} CAS(old_b: bool, new_b: bool) returns (success: bool);

////////////////////////////////////////////////////////////////////////////////

function {:builtin "MapConst"} MapConstBool(bool): [Tid]bool;
function {:builtin "MapOr"} MapOr([Tid]bool, [Tid]bool) : [Tid]bool;

function {:inline} {:linear "tid"} TidCollector(x: Tid) : [Tid]bool
{
  MapConstBool(false)[x := true]
}
function {:inline} {:linear "tid"} TidSetCollector(x: [Tid]bool) : [Tid]bool
{
  x
}
```
