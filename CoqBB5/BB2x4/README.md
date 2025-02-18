# BB(2,4) = 3,932,964

This folder contains the Coq (v8.20.1) proof that `BB(2,4) = 3,932,964` (see `../README.md` for definitions). This result means that the maximum number of steps that a halting 2-state 4-symbol Turing machine can do is 3,932,964. 

Proving this results involves enumerating 2-state 4-symbol Turing machines and decide for each whether it halts or not and, if it halts, that it halts after at most 3,932,964 steps.

## Run the proof

In order to run the proof (assuming you have Coq v8.20.1 installed), do:

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

- Loops, see `../BB5/Deciders/Decider_Loop.v`
- n-gram Closed Position Set, see `../BB5/Deciders/Decider_NGramCPS.v`
- Repeated Word List, see `../BB5/Deciders/Decider_RepWL.v`
- Halt Max (run machines up to 3,932,964 steps), see `Deciders/Decider_Halt_BB2x4.v`

Each of these techniques is described in [bbchallenge's BB5 paper](https://github.com/bbchallenge/bbchallenge-paper).

The deciders' algorithms are programmed in Coq and then proved correct in Coq too (i.e. proving that if they output `HALT`/`NONHALT` on a machine then the machine halts/does not halt).

### Extracting results