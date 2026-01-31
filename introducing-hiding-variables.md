---
title: Introducing and Hiding Variables
nav_order: 3
---

In a multi-layered refinement proof it is not only useful to change the granularity of atomicity,
but also the state representation, i.e., the set of variables over which different program layers are expressed.
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
  call {:layer 1} y := Copy(x);
}

atomic action {:layer 1} atomic_read_x () returns (v:int)
{ v := x; }
yield procedure {:layer 0} read_x () returns (v:int)
refines atomic_read_x;
{
  call {:layer 0} v := Copy(x);
}

atomic action {:layer 1} atomic_write_x (x':int)
modifies x;
{ x := x'; }
yield procedure {:layer 0} write_x (x':int)
refines atomic_write_x;
{
  call {:layer 0} x := Copy(x');
}
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
To express our intention for `y` we call the action `Copy`,
a pure action defined in the Civl base library which copies its input into its output.
We often use calls to `Copy`, together with a layer annotation to introduce computation.
This particular call sets `y` to the current value of `x`, which at the time of invocation is `y'`.
Thus we get `y == y'` and we can prove that `write_y` refines `atomic_write_y`.

Invocation of `Copy` has the specific purpose of assigning meaning to introduced variables.
Such a call is a kind of ghost code that does not cause a context switch;
recall that `atomic_write_x` and `Copy` need to execute without context switch to ensure `y == y'`.

We have the following layering constraints:

* An action can access any global variable that exists throughout the layer range of the action.
For example, `x` is introduced at layer 0 before `atomic_read_x` at layer 1, and is hidden at layer 1 together with `atomic_read_x`.
It is not permissible to introduce `atomic_read_x` at layer 0.
* A pure action may not access any global variable and must not block.
A pure action may be directly called by a yield procedure to introduce computation at a layer indicated by an attribute `{:layer n}` on the call.
For such a call, the inputs may refer to any variable that exists at `n` or is introduced at `n`.
Any output of the call must be received in a variable that is introduced at `n`.

Variable introduction and hiding create the possibility of two different
programs at each layer, called the low program and the high program of the layer.
The high program at layer n contains all the code of the low program at n together with
calls to actions without mover types that introduce variables at layer n.
Neither the low nor the high program at layer n contains the variables hidden at n.
The variables introduced at layer n and the actions that introduce them
are present in the high program but not the low program at layer n.
Refinement checking at a layer is performed on the high program of that layer.

The detailed example in the section on
[Layered Concurrent Programs](https://civl-verifier.github.io/layered-concurrent-programs.html)
only showed the high program at each layer.
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
