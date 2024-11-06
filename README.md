# Coq-BB5

Coq-BB5 (author: [ccz181078/mxdys](https://github.com/ccz181078)) proves theorem in Coq about [Busy Beaver values](https://wiki.bbchallenge.org/wiki/Main_Page), including the following results:

- `BB(5) = 47,176,870`
- `BB(2,4) = 3,932,964`
- `BB(4) = 107`

See the `CoqBB5` folder.

Coq-BB5 relies on the [busycoq](https://github.com/meithecatte/busycoq/tree/333695b79707189d49f5e560a55c3ab8dda1cdc6) library (author: [meithecatte](https://github.com/meithecatte)) for proving that some individual 5-state 2-symbol Turing machines do not halt. The `BusyCoq` folder contains a partial snapshot of `busycoq`, i.e. only the proofs that are used in `Coq-BB5`.

## Usage

Assuming that you have [installed Coq](https://github.com/coq/coq/blob/master/INSTALL.md), you can run `make` at the root of this repository which will first compile `BusyCoq` and then `CoqBB5`. Equivalently you can run `make` first in the `BusyCoq` folder and then in the `CoqBB5` folder.