# BB(2,4) = 3,932,964

This folder contains the Coq (v8.20.1) proof that `BB(2,4) = 3,932,964` (see `../README.md` for definitions). This result means that the maximum number of steps that a halting 2-state 4-symbol Turing machine can do is 3,932,964. 

Proving this results involves enumerating 2-state 4-symbol Turing machines and decide for each whether it halts or not and, if it halts, that it halts at most after 3,932,964 steps.

In order to run the proof (assuming you have Coq installed), do:

```
./create_proof_files.sh
make
```

## Proof structure

The main definitions and `BB(2,4) = 3,932,964` theorem statement are in `BB2x4_Statement.v` (this file does not require much Coq knowledge to be understood). The entry-point of the proof is located in `BB2x4_Theorem.v`.

### Tree Normal Form (TNF) enumeration

The proof enumerates 2-state 4-symbol machines in [Tree Normal Form](https://wiki.bbchallenge.org/wiki/Tree_Normal_Form) (**TNF**). Each enumerated machine is passed through a pipeline of deciders which are algorithm trying to prove whether the machine halts or not:

- If the machine halts, i.e. meets an undefined transition, a new subtree of machines is visited for all the possible ways to fill the undefined transition
- If the machine does not halt, it is a leaf of the TNF tree

The TNF enumeration algorithm is located in `BB2x4_TNF_Enumeration.v`.

### Deciders

Deciders are algorithms trying to prove whether a given Turing machine halts or not. The pipeline of deciders used to solve `BB(2,4)` (pipeline defined in `BB2x4_Deciders_Pipeline.v`) is:

- Loops
- n-gram Closed Position Set
- Repeated Word List
- Halt Max (run machines up to 3,932,964 steps)

Each of these techniques is described in [bbchallenge's BB5 paper](https://github.com/bbchallenge/bbchallenge-paper).

The deciders' algorithms (present in `Deciders/` once you have run `./create_proof_files.sh` which copies them from `../BB5/Deciders/`) are programmed in Coq and then proved correct in Coq too.

### Extracting results