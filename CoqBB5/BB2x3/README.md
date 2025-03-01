# BB(2,3) = 38

This folder contains the Coq ([v8.20.1](https://github.com/coq/coq/blob/V8.20.1/INSTALL.md)) proof that `BB(2,3) = 38`. This result was first proved, in [[Lafitte and Papazian, 2007]](https://arxiv.org/pdf/0906.3749).

This result means that the maximum number of steps that a halting 2-state 3-symbol Turing machine can do from all-0 tape is 38. See [bbchallenge's wiki](https://wiki.bbchallenge.org/wiki/Main_Page) or [bbchallenge's BB5 paper](https://github.com/bbchallenge/bbchallenge-paper) for more background and detailed information.

Proving this results involves enumerating 2-state 3-symbol Turing machines and deciding for each whether it halts or not and, if it halts, that it halts in at most 38 steps.

The extracted data from this proof is available at [https://docs.bbchallenge.org/CoqBB5_release_v1.0.0/BB2x3_verified_enumeration.csv](https://docs.bbchallenge.org/CoqBB5_release_v1.0.0/BB2x3_verified_enumeration.csv) in the form of a CSV file listing each enumerated machine with its halting status (halt/nonhalt) as well as the ID of the decider that decided it (IDs as defined in `BB2x3_Deciders_Generic.v`). More details [below](#extracting-results).

## Compiling the proof

Assuming you have [opam installed](https://opam.ocaml.org/doc/Install.html), you can install Coq v8.20.1 using:

```sh
opam switch create 4.14.2 # if already existent do: opam switch 4.14.2
eval $(opam env)
opam install coq-native
opam pin add coq 8.20.1
```

Then, in order to compile the proof, do:

```sh
make
```

### Used Axiom

As outputted at the end of the compilation, the proof only depends on Coq's standard library axiom [functional_extensionality_dep](https://coq.inria.fr/doc/v8.9/stdlib/Coq.Logic.FunctionalExtensionality.html):

```Coq
Axiom functional_extensionality_dep : forall {A} {B : A -> Type},
  forall (f g : forall x : A, B x),
  (forall x, f x = g x) -> f = g.
```

This axiom is used to simplify the equality between `TM` and `ExecState` (both defined in `BB2x3_Statement.v`) since they are represented by functions[^1]. 

## Proof structure

The main definitions and `BB(2,3) = 38` theorem statement are in `BB2x3_Statement.v` (this file does not require much Coq knowledge to be understood). The entry-point of the proof is located in `BB2x3_Theorem.v`.

### Tree Normal Form (TNF) enumeration

The proof enumerates 2-state 3-symbol machines in [Tree Normal Form](https://wiki.bbchallenge.org/wiki/Tree_Normal_Form) (**TNF**). Each enumerated machine is passed through a pipeline of deciders which are algorithm trying to prove whether the machine halts or not:

- If the machine halts, i.e. meets an undefined transition, a new subtree of machines is visited for all the possible ways to fill the undefined transition
- If the machine does not halt, it is a leaf of the TNF tree

The TNF enumeration terminates when all leafs have been reached, i.e. all the enumerated Turing machines have been decided and there are no more halting machines to expand into subtrees.

The TNF enumeration algorithm is located in `BB2x3_TNF_Enumeration.v`.

**Technicalities:** the implemented TNF enumeration safely ignores machines whose first head move direction is `Left` since they can be symmetrised to use `Right` instead. However, contrarily to other implementations (such as [TNF-1RB](https://wiki.bbchallenge.org/wiki/Tree_Normal_Form#TNF-1RB)), this enumeration contains both machines that start by writing a `0` and those that start by writing a `1`, yielding a bigger search space but a simpler proof.  

### Deciders

Deciders are algorithms trying to prove whether a given Turing machine halts or not. The pipeline of deciders used to solve `BB(2,3)` (pipeline defined in `BB2x3_Deciders_Pipeline.v`) is a subset of the `BB(5)` pipeline (see ../BB5):

1. Loops, see `../BB5/Deciders/Decider_Loop.v`
2. n-gram Closed Position Set (n-gram CPS), see `../BB5/Deciders/Decider_NGramCPS.v`
3. Repeated Word List (RepWL), see `../BB5/Deciders/Decider_RepWL.v`

Each of these techniques is described at length in [bbchallenge's BB5 paper](https://github.com/bbchallenge/bbchallenge-paper), also see `../BB5/Deciders/README.md` and the comments in each file listed above for some information.

The deciders' algorithms are programmed in Coq and then proved correct in Coq too (i.e. proving that if they output `HALT`/`NONHALT` on a machine then the machine halts/does not halt).

### Extracting results

The list of all enumerated machines (using [bbchallenge format](https://discuss.bbchallenge.org/t/standard-tm-text-format/60/28?u=cosmo)) with for each, halting status and decider ID can be extracted from the Coq proof by doing (once you've compiled the proof):

```sh
cd BB2x3_Extraction
./BB2x3_Extraction.sh
```

Which should produce the file `BB2x3_verified_enumeration.csv` with shasum ending in `...2040a0d5` and file starting with:

```
machine,status,decider
---------_---------,halt,LOOP1_params_38
0RA------_---------,nonhalt,LOOP1_params_38
1RA------_---------,nonhalt,LOOP1_params_38
2RA------_---------,nonhalt,LOOP1_params_38
0RB------_---------,halt,LOOP1_params_38
0RB------_0LA------,nonhalt,LOOP1_params_38
0RB------_1LA------,halt,LOOP1_params_38
0RB------_1LA0LA---,nonhalt,LOOP1_params_38
0RB------_1LA1LA---,nonhalt,LOOP1_params_38
...
```

This step relies on OCaml extraction of the Coq code (specified in `BB2x3_Extraction.v`).

See `BB2x3_Extraction/README.md` for more information and troubleshooting.

This extracted `BB2x3_verified_enumeration.csv` is also available at [https://docs.bbchallenge.org/CoqBB5_release_v1.0.0/](https://docs.bbchallenge.org/CoqBB5_release_v1.0.0/).

### Results

The proof enumerates **6,019** machines, here are the summarized counts (computed from [the CSV extraction](https://docs.bbchallenge.org/CoqBB5_release_v1.0.0/BB2x3_verified_enumeration.csv)) of decided machines per decider:

| Decider                    | Nonhalt | Halt  | Total |
| -------------------------- | ------- | ----- | ----- |
| Loops                      | 3,861   | 1,816 | 5,677 |
| n-gram Closed Position Set | 332     |       | 332   |
| Repeated Word List         | 10      |       | 10    |
| Total                      | 4,203   | 1,816 | 6,019 |

Here are more precise counts exactly following the pipeline used by the proof (`BB2x3_Deciders_Pipeline.v`). Deciders IDs are the same as defined in `BB2x3_Deciders_Generic.v` which contains parameters information:

| Decider ID                     | Nonhalt | Halt  | Total |
| ------------------------------ | ------- | ----- | ----- |
| LOOP1_params_38                | 3,861   | 1,816 | 5,677 |
| NGRAM_CPS_IMPL2_params_1_1_400 | 288     |       |       |
| NGRAM_CPS_IMPL2_params_2_2_800 | 36      |       |       |
| NGRAM_CPS_IMPL2_params_3_3_400 | 8       |       |       |
| REPWL_params_2_3_320_400       | 10      |       |       |
| Total                          | 4,203   | 1,816 | 6,019 |

## Files index

- `BB2x3_Deciders_Generic.v`: deciders IDs definition
- `BB2x3_Deciders_Pipeline.v`: decider pipeline definition and lemmas
- `BB2x3_Encodings.v`: routines that encode objects into numbers for fast lookup using Coq's `FSets.FMapPositive`
- `BB2x3_Extraction.v`: OCaml extraction, see [above](#extracting-results)
- `BB2x3_Make_TM.v`: mainly routines to build 2-state 3-symbol Turing machines
- `BB2x3_Statement.v`: main definition and `BB(2,3) = 38` theorem statement
- `BB2x3_Theorem.v`: entry point of the proof of `BB(2,3) = 38`
- `BB2x3_TNF_Enumeration.v`: Tree Normal Form enumeration of 2-state 3-symbol Turing machines
- `BB2x3_Extraction/BB2x3_Extraction.sh`: compiles the OCaml extraction, runs it and saves results to [BB2x3_verified_enumeration.csv](https://docs.bbchallenge.org/CoqBB5_release_v1.0.0/) (also checks hashes)

### Files copied from ../BB5

The following files are copied from `../BB5` after running `copy_from_BB5.sh` (the script also modifies Coq files' import statements using `sed`):

- `List_Routines.v`: routines to manipulate lists
- `List_Tape.v`: routines to manipulate Turing machines tapes as lists
- `Prelims.v`: various definitions of general interest
- `Tactics.v`: custom Coq tactics
- `TM.v`: tools to work with Turing Machines
- `TNF.v`: tools for the Tree Normal Form enumeration (e.g. `SearchQueue` implementation etc...)

- `Deciders/Deciders_Common.v`: common abstraction needed by deciders
- `Deciders/Decider_Halt.v`: decider that detects halting by running a machine for some steps
- `Deciders/Decider_Halt_BB2x3.v`: Halt Max decider, runs machines up to 38 steps and detects halting
- `Deciders/Decider_Loop.v`: decider for loops
- `Deciders/Decider_NGramCPS.v`: n-gram Closed Position Set decider
- `Deciders/Decider_RepWL.v`: Repeated Word List decider
- `Deciders/Verifier_Halt.v`: verifier that a machine does halt after a given number of steps

The deciders are described at length in [bbchallenge's BB5 paper](https://github.com/bbchallenge/bbchallenge-paper), also see `../BB5/Deciders/README.md` and the comments in each file listed above for some information.

#### Note to maintainers

Maintainers and programmers of this repo must re-run `./copy_from_BB5.sh` when changing these files in `../BB5` in order to make sure they are propagated here.

[^1]: Removing this axiom would introduce [Setoid](https://coq.inria.fr/doc/v8.9/stdlib/Coq.Setoids.Setoid.html) everywhere.