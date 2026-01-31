---
title: Synchronizing Asynchrony
nav_order: 8
---


In this section, we focus on Civl features for synchronizing asynchronous procedure calls.

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