# Coq-BB5

Coq-BB5 (author: [ccz181078/mxdys](https://github.com/ccz181078)) proves theorem in Coq about [Busy Beaver values](https://wiki.bbchallenge.org/wiki/Main_Page), including the following results:

- `BB(5) = 47,176,870`
- `BB(2,4) = 3,932,964`
- `BB(4) = 107`

See the `CoqBB5` folder.

Coq-BB5 relies on the [busycoq](https://github.com/meithecatte/busycoq/tree/333695b79707189d49f5e560a55c3ab8dda1cdc6) library (author: [meithecatte](https://github.com/meithecatte)) for proving that some individual 5-state 2-symbol Turing machines do not halt. The `BusyCoq` folder contains a partial snapshot of `busycoq`, i.e. only the proofs that are used in `Coq-BB5`.

## Usage

Assuming that you have [installed Coq](https://github.com/coq/coq/blob/master/INSTALL.md), the following command will compile the proof of `BB(5) = 47,176,870` (see `CoqBB5/README.md` for compiling the other results):

```
cd BusyCoq && make -j 13 && cd ../CoqBB5 && make -j 13
```

Replace `13` with the number of cores you want to use.

The proof will compile in about 45 minutes with 13 cores using `native_compute` (`opam install coq-native`) and in about 3 hours using `vm_compute` and consume in all cases about 4Gb of RAM.