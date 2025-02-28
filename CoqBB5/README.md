# Coq-BB5

Coq-BB5 (author: [mxdys](https://github.com/ccz181078)) proves theorem in Coq ([v8.20.1](https://github.com/coq/coq/blob/V8.20.1/INSTALL.md)) about [Busy Beaver values](https://wiki.bbchallenge.org/wiki/Main_Page), including the following results:

Original results:
- `BB(5) = 47,176,870`, see [BB5/](BB5/)
- `BB(2,4) = 3,932,964`, see [BB2x4/](BB2x4/)

Previously known:
- `BB(4) = 107`, see [BB4/](BB4/)
- `BB(3) = 21`, see [BB3/](BB3/)
- `BB(2) = 6`, see [BB2/](BB2/)
- `BB(2,3) = 38`, see [BB2x3/](BB2x3/)

## Structure of the proofs

The [proof of BB(5)](BB5/) is the most general one in the sense that:

1. All the other proofs only use subsets of the techniques used to prove BB(5).
2. All the other proofs use the same overall [structure than the BB(4) proof](BB4/README.md#proof-structure), which is itself a slight simplification of the [structure than the BB(5) proof](BB5/README.md#proof-structure).