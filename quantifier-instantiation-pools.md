---
title: Quantifier-Instantiation Pools
nav_order: 8
---

The attributes `:pool` and `:add_to_pool`
are used to provide hints for instantiating quantifiers,
which are a notorious source of incompleteness and unpredictable performance in SMT solvers.
In this section, we explain the use of these attributes.

We introduce these attributes using the following simpler example.

```boogie
function F(int): bool;

procedure A0()
{
  assume (forall {:pool "L"} x: int :: F(x-1));
  assert {:add_to_pool "L", 1} F(0);
  assert (forall y: int :: {:add_to_pool "L", y+1} F(y));
}
```

To prove the first assert in procedure `A0`, the quantifier in the assume statement must be instantiated at 1.
Without the pool hints, this assert will not be verified because the SMT solver underlying Boogie is unable to deduce the usefulness of this instantiation.
To help with quantifier instantiation, we use instantiation pools where each pool is a set of terms.
This example uses a single pool `"L"`.
A bound variable expresses interest in being instantiated by terms in `"L"` by using the attribute `:pool "L"`.
Terms are added to a pool using the attribute `:add_to_pool`.
For example, the first assert statement adds the term `1` to the pool `"L"`.

The second assert statement illustrates a more sophisticated use of instantiation pools.
Unlike the first assert statement, the expression is this assert has a universal quantifier.
The verification condition generator in Boogie detects that this quantifier may be skolemized using a fresh constant `y0`.
The `add_to_pool` hint in the body of the quantifier tells Boogie to add the term `y0+1` to the pool `"L"`.
Another way to think about this explanation is that Boogie automatically generates the following intermediate program
whose correctness implies the correctness of the original program.

```boogie
function F(int): bool;

procedure A0()
{
  var y0: int;
  assume (forall {:pool "L"} x: int :: F(x-1));
  assert {:add_to_pool "L", 1} F(0);
  assert {:add_to_pool "L", y0+1} F(y0);
}
```

The following example shows how instantiation pools handle nested quantifiers.
In this example, two pools ```"A"``` and ```"B"``` are used.

```boogie
function P(int, int): bool;
procedure B1()
{
  assume (exists x: int :: {:add_to_pool "B", x+1} (forall {:pool "A"} y: int :: P(x,y)));
  assert (forall y: int :: {:add_to_pool "A", y} (exists {:pool "B"} x: int :: P(x-1,y)));
}
```

Ignoring the pool annotations, the verification problem amounts to proving the following implication,
where the bound variables ```x``` and ```y``` have been renamed to distinguish their use
in the antecedent and the consequent:

```
(exists x1: int :: (forall y1: int :: P(x1,y1)))
==>
(forall y2: int :: (exists x2: int :: P(x2-1,y2)))
```

The following proof steps are automatically carried out by Boogie using the instantiation hints:
- skolemize ```x1``` to ```x1'``` and ```y2``` to ```y2'```
- add ```x1'+1``` to pool ```"B"``` and ```y2'``` to pool ```"A"```
- instantiate ```y1``` with ```y2'``` and ```x2``` with ```x1'+1```

Each local variable of an atomic action may also be annotated with the `:pool ...` attribute. 
For each action, Civl internally generates a transition relation that existentially quantifies nondeterministically-initialized local variables.
The pool hints on local variables of actions are targeted towards this internally-generated quantifier.
