# Coq-BB5

Coq-BB5 (author: [mxdys](https://github.com/ccz181078)) proves theorem in Coq ([v8.20.1](https://github.com/coq/coq/blob/V8.20.1/INSTALL.md)) about [Busy Beaver values](https://wiki.bbchallenge.org/wiki/Main_Page), including the following results:

Original results:
- `BB(5) = 47,176,870`, see [CoqBB5/BB5/](CoqBB5/BB5/)
- `BB(2,4) = 3,932,964`, see [CoqBB5/BB2x4/](CoqBB5/BB2x4/)

Previously known:
- `BB(4) = 107`, see [CoqBB5/BB4/](CoqBB5/BB4/)

## BusyCoq

For the proof of `BB(5) = 47,176,870`, Coq-BB5 relies on the [busycoq](https://github.com/meithecatte/busycoq/tree/333695b79707189d49f5e560a55c3ab8dda1cdc6) library (author: [meithecatte](https://github.com/meithecatte)) for proving that some individual 5-state 2-symbol Turing machines do not halt. The `BusyCoq/` folder contains a partial snapshot of `busycoq`, i.e. only the proofs that are used in `Coq-BB5/BB5/`.