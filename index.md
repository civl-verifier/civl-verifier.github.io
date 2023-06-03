Civl is a verifier for concurrent programs following two core design principles.

* **Layered Refinement** (instead of monolithic proofs): Programs are verified
  across multiple layers of stacked refinements.
  Each refinement layer corresponds to a simplifying program transformation.
  Proof construction becomes more productive by decomposing the problem into small,
  manageable, and automatable pieces.
  The resulting proofs become simpler and easier to reuse.

* **Structured Programs** (instead of transition systems): Each layer of
  abstraction (from low-level implementations to high-level specifications) is
  represented in the same language of structured programs. This naturally
  bridges the verification gap down to implementations and enables the
  utilization of program structure in proofs. All layers (and their connection)
  are compactly expressed together as a single syntactic unit in a
  *[layered concurrent program](https://doi.org/10.1007/978-3-319-96145-3_5)*.

Civl supports established verification techniques for
concurrent programs, including
*stepwise-refinement*,
*[gated atomic actions](https://doi.org/10.1145/1480881.1480885)*,
*[mover types](https://doi.org/10.1145/781131.781169)*,
*inductive invariants*, *noninterference reasoning*,
and *linear permissions*.
It also incorporates newer
verification techniques and methodologies, like
*[yield invariants](https://doi.org/10.1007/978-3-030-53288-8_14)*,
*[inductive sequentialization](https://doi.org/10.1145/3385412.3385980)*,
and *[synchronization](https://dx.doi.org/10.4230/LIPIcs.CONCUR.2018.21)*.

Civl is built as a conservative extension of
[Boogie](https://github.com/boogie-org/boogie), a verifier for sequential
programs. Civl decomposes proof checking into modular verification conditions
that are automatically verified by a theorem prover/SMT solver.

# Getting Started

Civl is implemented as part of [Boogie](https://github.com/boogie-org/boogie),
which can be installed from a [NuGet package](https://www.nuget.org/packages/Boogie) or
[built from source](https://github.com/boogie-org/boogie#building), and requires the
[Z3](https://github.com/Z3Prover/z3) theorem prover.

To verify a Civl program, simply invoke Boogie on the program as follows:

```
$ boogie Test/civl/ticket.bpl

Boogie program verifier finished with 19 verified, 0 errors
```

To inspect the plain Boogie program that Civl generates, use the option `-civlDesugaredFile:<file.bpl>`.
Further available options are listed by `-help`.

# Resources

We have a [tutorial](doc) to help users get started with Civl.
We also recommend looking at simple
examples from our [test suite](https://github.com/boogie-org/boogie/tree/master/Test/civl),
like `Program*.bpl`, `cav2020-*.bpl`, and `freund.bpl`.
Other notable Civl examples include
a [verified garbage collector](https://github.com/boogie-org/boogie/blob/master/Test/civl/GC.bpl),
lock implementations
([spinlock](https://github.com/boogie-org/boogie/blob/master/Test/civl/lock-introduced.bpl),
[ticket](https://github.com/boogie-org/boogie/blob/master/Test/civl/ticket.bpl),
[seqlock](https://github.com/boogie-org/boogie/blob/master/Test/civl/seqlock.bpl)),
concurrent data structures
([Treiber stack](https://github.com/boogie-org/boogie/blob/master/Test/civl/treiber-stack.bpl),
[FastTrack vector clocks](https://github.com/boogie-org/boogie/blob/master/Test/civl/verified-ft.bpl)),
distributed protocols
([Paxos](https://github.com/boogie-org/boogie/tree/master/Test/civl/inductive-sequentialization/paxos),
[two-phase commit](https://github.com/boogie-org/boogie/blob/master/Test/civl/inductive-sequentialization/2PC.bpl) /
[2PC](https://github.com/boogie-org/boogie/blob/master/Test/civl/async/2pc.bpl),
[Chang-Roberts](https://github.com/boogie-org/boogie/blob/master/Test/civl/inductive-sequentialization/ChangRoberts.bpl)),
and many more.

## Publications

* [The Civl Verifier](papers/fmcad2021.pdf)\
  Bernhard Kragl, Shaz Qadeer\
  FMCAD 2021
* [Refinement for Structured Concurrent Programs](papers/cav2020.pdf)\
  Bernhard Kragl, Shaz Qadeer, Thomas A. Henzinger\
  CAV 2020
* [Inductive Sequentialization of Asynchronous Programs](papers/pldi2020.pdf)\
  Bernhard Kragl, Constantin Enea, Thomas A. Henzinger, Suha Orhun Mutluergil, Shaz Qadeer\
  PLDI 2020
* [Synchronizing the Asynchronous](papers/concur2018.pdf)\
  Bernhard Kragl, Shaz Qadeer, Thomas A. Henzinger\
  CONCUR 2018
* [Layered Concurrent Programs](papers/cav2018.pdf)\
  Bernhard Kragl, Shaz Qadeer\
  CAV 2018
* [Automated and Modular Refinement Reasoning for Concurrent Programs](https://www.microsoft.com/en-us/research/publication/automated-and-modular-refinement-reasoning-for-concurrent-programs/)\
  Chris Hawblitzel, Erez Petrank, Shaz Qadeer, Serdar Tasiran\
  CAV 2015

## Talks

* [The Civl Verifier](https://youtu.be/vGMnQqoy6eA) @ FMCAD 2021
* [Reifying Concurrent Programs](https://bbb-lb.math.univ-paris-diderot.fr/playback/presentation/2.3/972f09fb375ed24cd2f676ef7a70c4bbea355455-1614264363134?meetingId=972f09fb375ed24cd2f676ef7a70c4bbea355455-1614264363134) @ University of Paris VII
* [Refinement for Structured Concurrent Programs](https://youtu.be/anKt3qjo5as?t=1306) @ CAV 2020
* [Civl-ized Concurrent Programs](https://youtu.be/f8Cjpt-rzxE?t=2081) @ [DSV 2020](https://smackers.github.io/democratizing-software-verification-workshop-2020/)
* [Inductive Sequentialization of Asynchronous Programs](https://www.youtube.com/watch?v=hShxxspWeb8) @ PLDI 2020

# Team

* [Bernhard Kragl](https://bkragl.github.io)
* [Shaz Qadeer](https://scholar.google.com/citations?user=EqIVfYcAAAAJ&hl=en)

If you are interested in Civl, please get in touch!
