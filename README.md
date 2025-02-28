# Coq-BB5

Coq-BB5 (author: [mxdys](https://github.com/ccz181078)) proves theorem in Coq ([v8.20.1](https://github.com/coq/coq/blob/V8.20.1/INSTALL.md)) about [Busy Beaver values](https://wiki.bbchallenge.org/wiki/Main_Page), including the following results:

Original results:
- `BB(5) = 47,176,870`, see [CoqBB5/BB5/](CoqBB5/BB5/)
- `BB(2,4) = 3,932,964`, see [CoqBB5/BB2x4/](CoqBB5/BB2x4/)

Previously known:
- `BB(4) = 107`, see [CoqBB5/BB4/](CoqBB5/BB4/)
- `BB(3) = 21`, see [CoqBB5/BB3/](CoqBB5/BB3/)
- `BB(2) = 6`, see [CoqBB5/BB2/](CoqBB5/BB2/)
- `BB(2,3) = 38`, see [CoqBB5/BB2x3/](CoqBB5/BB2x3/)

The [proof of BB(5)](CoqBB5/BB5/) is the most general one in the sense that:

1. All the other proofs only use subsets of the techniques used to prove BB(5).
2. All the other proofs use the same overall [structure of the BB(4) proof](CoqBB5/BB4/README.md#proof-structure), which is itself a slight simplification of the [structure of the BB(5) proof](CoqBB5/BB5/README.md#proof-structure).

## BusyCoq

For the proof of `BB(5) = 47,176,870`, Coq-BB5 relies on the [busycoq](https://github.com/meithecatte/busycoq/tree/333695b79707189d49f5e560a55c3ab8dda1cdc6) library (author: [meithecatte](https://github.com/meithecatte)) for proving that some individual 5-state 2-symbol Turing machines, called [Sporadic Machines](CoqBB5/BB5/README.md#sporadic-machines), do not halt. The `BusyCoq/` folder contains a partial snapshot of `busycoq`, i.e. only the proofs that are used in `CoqBB5/BB5/`.