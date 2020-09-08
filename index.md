CIVL is a verifier for concurrent programs following two core design principles.

* **Layered Refinement** (instead of monolithic proofs): Programs are verified
  across multiple layers of refinement, where each refinement step corresponds
  to a small simplifying program transformation. Proof construction becomes more
  productive by decomposing the problem into small, manageable, and automatable
  pieces, and the resulting proofs become simpler and easier to reuse.

* **Structured Programs** (instead of transition systems): Each layer of
  abstraction (from low-level implementations to high-level specifications) is
  represented in the same language of structured programs. This naturally
  bridges the verification gap down to implementations and enables the
  utilization of program structure in proofs. All layers (and their connection)
  are compactly expressed together as a single syntactic unit in a *layered
  concurrent program*.

CIVL supports a unique blend of established verification techniques for
concurrent programs, including
*stepwise-refinement*,
*[gated atomic actions](https://doi.org/10.1145/1480881.1480885)*,
*mover types (à la Lipton's reduction)*,
*inductive invariants* (noninterference reasoning à la Owicki-Gries and rely-guarantee),
and *linear permissions*.
Furthermore, it is the driver and testbed for cutting-edge research on novel
verification techniques and methodologies, like
*yield invariants*,
*inductive sequentialization*,
and *synchronization*.

Under the hood, CIVL is built on top of
[Boogie](https://github.com/boogie-org/boogie), a verifier for sequential
programs. CIVL decomposes proof checking into modular verification conditions
that are automatically verified by a theorem prover/SMT solver.

# Getting Started

CIVL is implemented directly as part of [Boogie](https://github.com/boogie-org/boogie),
which can be installed from a [NuGet package](https://www.nuget.org/packages/Boogie) or
[built from source](https://github.com/boogie-org/boogie#building), and requires the
[Z3](https://github.com/Z3Prover/z3) theorem prover.

To verify a CIVL program, simply invoke Boogie on the program as follows
(CIVL programs typically use Z3's generalized array theory, enabled by `-useArrayTheory`):

```
$ boogie -nologo -useArrayTheory Test/civl/ticket.bpl

Boogie program verifier finished with 19 verified, 0 errors
```

To inspect the plain Boogie program that CIVL generates, use the option `-civlDesugaredFile:<file.bpl>`.
Further available options are listed by `-help`.

# Resources

## Examples

CIVL comes with an extensive [test suite](https://github.com/boogie-org/boogie/tree/master/Test/civl)
of example programs, including
a [verified garbage collector](https://github.com/boogie-org/boogie/blob/master/Test/civl/GC.bpl),
the [VerifiedFT dynamic race detector](https://github.com/boogie-org/boogie/blob/master/Test/civl/verified-ft.bpl),
lock implementations
([spinlock](https://github.com/boogie-org/boogie/blob/master/Test/civl/lock-introduced.bpl),
[ticket](https://github.com/boogie-org/boogie/blob/master/Test/civl/ticket.bpl),
[seqlock](https://github.com/boogie-org/boogie/blob/master/Test/civl/seqlock.bpl)),
concurrent data structures
([treiber stack](https://github.com/boogie-org/boogie/blob/master/Test/civl/treiber-stack.bpl),
[work stealing queue](https://github.com/boogie-org/boogie/blob/master/Test/civl/wsq.bpl)),
distributed protocols
([Paxos](https://github.com/boogie-org/boogie/tree/master/Test/civl/inductive-sequentialization/paxos),
[two-phase commit](https://github.com/boogie-org/boogie/blob/master/Test/civl/inductive-sequentialization/2PC.bpl) /
[2PC](https://github.com/boogie-org/boogie/blob/master/Test/civl/async/2pc.bpl),
[Chang-Roberts](https://github.com/boogie-org/boogie/blob/master/Test/civl/inductive-sequentialization/ChangRoberts.bpl)),
and many more.

## [Tutorial (under construction)](tutorial)

Until the CIVL tutorial becomes available, we recommend to have a look at simple
examples from our [test suite](https://github.com/boogie-org/boogie/tree/master/Test/civl),
like `Program*.bpl`, `cav2020-*.bpl`, and `freund.bpl`.

## Publications

* [Refinement for Structured Concurrent Programs](https://pub.ist.ac.at/~bkragl/papers/cav2020.pdf)\
  Bernhard Kragl, Shaz Qadeer, Thomas A. Henzinger\
  CAV 2020
* [Inductive Sequentialization of Asynchronous Programs](https://pub.ist.ac.at/~bkragl/papers/pldi2020.pdf)\
  Bernhard Kragl, Constantin Enea, Thomas A. Henzinger, Suha Orhun Mutluergil, Shaz Qadeer\
  PLDI 2020
* [Synchronizing the Asynchronous](https://pub.ist.ac.at/~bkragl/papers/concur2018.pdf)\
  Bernhard Kragl, Shaz Qadeer, Thomas A. Henzinger\
  CONCUR 2018
* [Layered Concurrent Programs](https://pub.ist.ac.at/~bkragl/papers/cav2018.pdf)\
  Bernhard Kragl, Shaz Qadeer\
  CAV 2018
* [Automated and Modular Refinement Reasoning for Concurrent Programs](https://www.microsoft.com/en-us/research/publication/automated-and-modular-refinement-reasoning-for-concurrent-programs/)\
  Chris Hawblitzel, Erez Petrank, Shaz Qadeer, Serdar Tasiran\
  CAV 2015

## Talks

* [Refinement for Structured Concurrent Programs](https://youtu.be/anKt3qjo5as?t=1306) @ CAV 2020
* [CIVL-ized Concurrent Programs](https://youtu.be/f8Cjpt-rzxE?t=2081) @ [DSV 2020](https://smackers.github.io/democratizing-software-verification-workshop-2020/)
* [Inductive Sequentialization of Asynchronous Programs](https://www.youtube.com/watch?v=hShxxspWeb8) @ PLDI 2020

# Team

* [Bernhard Kragl (IST Austria)](https://pub.ist.ac.at/~bkragl)
* [Shaz Qadeer (Novi)](https://scholar.google.com/citations?user=EqIVfYcAAAAJ&hl=en)

If you are interested in CIVL, please get in touch! We are happy to give talks, lectures, and demos.
