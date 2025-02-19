# BB(5) = 47,176,870

This folder contains the Coq ([v8.20.1](https://github.com/coq/coq/blob/V8.20.1/INSTALL.md)) proof that `BB(5) = 47,176,870`. This result was not previously known.

This result means that the maximum number of steps that a halting 5-state Turing machine can do from all-0 tape is 47,176,870. See [bbchallenge's wiki](https://wiki.bbchallenge.org/wiki/Main_Page) or [bbchallenge's BB5 paper](https://github.com/bbchallenge/bbchallenge-paper) for more background and detailed information.

Proving this results involves enumerating 5-state Turing machines and deciding for each whether it halts or not and, if it halts, that it halts in at most 47,176,870 steps.

The extracted data from this proof is available at [https://docs.bbchallenge.org/CoqBB5_release_v1.0.0/BB5_verified_enumeration.csv.gz](https://docs.bbchallenge.org/CoqBB5_release_v1.0.0/BB5_verified_enumeration.csv.gz) in the form of a CSV file (**10 Gb**) listing each enumerated machine with its halting status (halt/nonhalt) as well as the ID of the decider that decided it (IDs as defined in `BB5_Deciders_Generic.v`). More details [below](#extracting-results).

## Compiling the proof

In order to compile the proof (assuming you have [Coq v8.20.1 installed](https://github.com/coq/coq/blob/V8.20.1/INSTALL.md)), do:

**Note:** replace `-j 13` by the number of cores you want to use.

```
cd ../../BusyCoq && make -j 13
cd ../CoqBB5/BB5 && make -j 13
```

Compiling BusyCoq is needed first in order to get proofs for 12 out the 13 [Sporadic Machines](#sporadic-machines). BusyCoq takes about 8 minutes on 13 cores (Apple silicon).

Then, compiling `CoqBB5/BB5` takes about 45 minutes on 13 cores (Apple silicon) and using Coq's `native_compute` (`opam install coq-native`).

### Used Axiom

As outputted at the end of the compilation, the proof only depends on Coq's standard library axiom [functional_extensionality_dep](https://coq.inria.fr/doc/v8.9/stdlib/Coq.Logic.FunctionalExtensionality.html):

```
functional_extensionality_dep
  : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
    (forall x : A, f x = g x) -> f = g
```

This axiom is used to simplify the equality between `TM` and `ExecState` (both defined in `BB5_Statement.v`) since they are represented by functions[^1]. 

## Proof structure

The main definitions and `BB(5) = 47,176,870` theorem statement are in `BB5_Statement.v` (this file does not require much Coq knowledge to be understood). The entry-point of the proof is located in `BB5_Theorem.v`.

### Tree Normal Form (TNF) enumeration (parallelised)

The proof enumerates 5-state machines in [Tree Normal Form](https://wiki.bbchallenge.org/wiki/Tree_Normal_Form) (**TNF**). Each enumerated machine is passed through a pipeline of deciders which are algorithm trying to prove whether the machine halts or not:

- If the machine halts, i.e. meets an undefined transition, a new subtree of machines is visited for all the possible ways to fill the undefined transition
- If the machine does not halt, it is a leaf of the TNF tree

The TNF enumeration terminates when all leafs have been reached, i.e. all the enumerated Turing machines have been decided and there are no more halting machines to expand into subtrees.

The TNF enumeration algorithm is located in `BB5_TNF_Enumeration.v`.

**Technicalities:** the implemented TNF enumeration safely ignores machines whose first head move direction is `Left` since they can be symmetrised to use `Right` instead. However, contrarily to other implementations (such as [bbchallenge's](https://bbchallenge.org/method) which implements [TNF-1RB](https://wiki.bbchallenge.org/wiki/Tree_Normal_Form#TNF-1RB)), this enumeration contains both machines that start by writing a `0` and those that start by writing a `1`, yielding a bigger search space but a simpler proof.  

#### Parallel compilation

In order to reach acceptable compile time, efforts were put into parellelising the compilation of the proof. Conveniently the *Tree* Normal Form enumeration builds a *tree* of Turing machines, hence parallel compilation was achieved by delegating subtrees to individual independent files which are located in `BB5_TNF_Enumeration_Roots`, see `BB5_TNF_Enumeration_Roots/README.md` for more details.

This technique could be iterated (i.e. break the tree in even more subtrees) to even further decrease compile time (provided enough cores).

**Note:** parallel compilation was not needed for the proofs of `BB(4)` and `BB(2,4)` (see `../BB4` and `../BB2x4`) whose search spaces are respectively about 200 and 100 times smaller than for `BB(5)` and whose proofs compile already quickly (about 30s for `BB(4)` and 2m30s for `BB(2,4)` on Apple silicon). As comparison, the unparallelised proof of `BB(5)` compiles in about 3 hours (on Apple silicon) with Coq's `native_compute` enabled (`opam install coq-native`), instead of about 45 minutes in the parallel version.

### Deciders

Deciders are algorithms trying to prove whether a given Turing machine halts or not. The pipeline of deciders used to solve `BB(5)` (pipeline defined in `BB5_Deciders_Pipeline.v`):

1. Loops, see `Deciders/Decider_Loop.v`
2. n-gram Closed Position Set (n-gram CPS), see `Deciders/Decider_NGramCPS.v`
3. Repeated Word List (RepWL), see `Deciders/Decider_RepWL.v`
4. Halt Max (run machines up to 47,176,870 steps), see `Deciders/Decider_Halt_BB5.v`
5. Finite Automata Reduction (FAR), **verifier**, see `Deciders/Verifier_FAR.v`
6. Weighted Finite Automata Reduction verification (WFAR), **verifier**, see `Deciders/Verifier_WFAR.v`

Each of these techniques is described at length in [bbchallenge's BB5 paper](https://github.com/bbchallenge/bbchallenge-paper), also see `Deciders/README.md` and the comments in each file listed above for some information.

The deciders' algorithms are programmed in Coq and then proved correct in Coq too (i.e. proving that if they output `HALT`/`NONHALT` on a machine then the machine halts/does not halt).

The exact order of the deciders (see [results](#results)) is chosen to decide most Turing machines efficiently.

The two techniques marked **verifier** (FAR and WFAR) have the specificity of *only* checking given nonhalting certificates rather than generating them (which is essentially what deciders do). There are 30 such certificates, given in `BB5_Deciders_Hardcoded_Parameters/Verifier_FAR_Hardcoded_Certificates.v` and `Verifier_WFAR_Hardcoded_Certificates.v`.

#### Generic VS Hardcoded parameters

More broadly than just for FAR and WFAR, the decider parameters (or verifier certificates) of 8,032 machines are **hardcoded**, meaning that the machines are all listed and for each of them, custom n-gram CPS / RepWL / Halt decider parameters are explicitely given (or FAR/WFAR certificates) rather than using generic parameters, applied to machines in bulk, as in `BB5_Deciders_Pipeline.v`. Specifically, in folder `BB5_Deciders_Hardcoded_Parameters/`, see:

- `Decider_Halt_Hardcoded_Parameters.v`
- `Decider_Loop_Hardcoded_Parameters.v`
- `Decider_NGramCPS_Hardcoded_Parameters.v`
- `Decider_RepWL_Hardcoded_Parameters.v`
- `Verifier_FAR_Hardcoded_Certificates.v`
- `Verifier_WFAR_Hardcoded_Certificates.v`

For instance, all 6,577 machines decided by RepWL (see [results](#results)) used hardcoded parameters, as listed in `BB5_Deciders_Hardcoded_Parameters/Decider_RepWL_Hardcoded_Parameters.v`.

Often, these parameters have been found by grid search implemented in other programming languages. The 30 FAR and WFAR certificates were provided by bbchallenge contributors.

**Note:** hardcoded parameters were not needed for the proofs of `BB(4)` and `BB(2,4)` (see `../BB4` and `../BB2x4`) which were entirely decided using generic parameters.

### Sporadic Machines

This pipeline leaves 13 machines undecided that we call 5-state Sporadic Machines (see `BB5_Sporadic_Machines.v`). We give individual nonhalting proofs for these machines. The proofs for 12 of the 13 machines (i.e. all except `BB5_Skelet17.v`) are imported from `BusyCoq`, (see `../../BusyCoq` and the [busycoq repository](https://github.com/meithecatte/busycoq/)).

**Note:** there were no sporadic machines for `BB(4)` and `BB(2,4)` (see `../BB4` and `../BB2x4`), i.e. no individual proofs of nonhalting.

Sporadic Machines were already present is [Skelet's 2003 bbfind holdouts](https://wiki.bbchallenge.org/wiki/Skelet) and are named in his honor:

- [Skelet's #1](https://bbchallenge.org/1RB1RD_1LC0RC_1RA1LD_0RE0LB_---1RC): Eventually repeats a translated pattern after at least $5.41 \times 10^{51}$ steps with period of 8,468,569,863 steps
- [Skelet's #10](https://bbchallenge.org/1RB0RA_0LC1RA_1RE1LD_1LC0LD_---0RB): [Double Fibonnaci Counter](https://www.sligocki.com/2023/03/14/skelet-10.html)
- [Skelet's #17](https://bbchallenge.org/1RB---_0LC1RE_0LD1LC_1RA1LB_0RB0RA): connected to [Gray code](https://en.wikipedia.org/wiki/Gray_code), see `BB5_Skelet17.md` and [https://arxiv.org/abs/2407.02426](https://arxiv.org/abs/2407.02426) and [https://wiki.bbchallenge.org/wiki/Skelet_17](https://wiki.bbchallenge.org/wiki/Skelet_17)
- Skelet's #15 #26 #33 #34 #35 : [Shift Overflow Counters](https://www.sligocki.com/2023/02/05/shift-overflow.html)

- 5 "[Finned machines](https://discuss.bbchallenge.org/t/bb5s-finned-machines-summary/234)" which had been claimed to be proven by hand by Skelet (Georgi Georgiev)

Proofs for all these machines except Skelet #17 were individually given in BusyCoq (see `../../BusyCoq` and the [busycoq repository](https://github.com/meithecatte/busycoq/)).

### Extracting results

The list of all enumerated machines (using [bbchallenge format](https://discuss.bbchallenge.org/t/standard-tm-text-format/60/28?u=cosmo)) with for each, halting status and decider ID can be extracted from the Coq proof by doing (once you've compiled the proof):

```
cd BB5_Extraction
./BB5_Extraction.sh
```

Which should run in about 2 hours (tested on Apple silicon) and produce the file `BB5_verified_enumeration.csv` (**10Gb**) with shasum ending in `...510583a39` and file starting with:

```
machine,status,decider
------_------_------_------_------,halt,LOOP1_params_130
0RA---_------_------_------_------,nonhalt,LOOP1_params_130
1RA---_------_------_------_------,nonhalt,LOOP1_params_130
0RB---_------_------_------_------,halt,LOOP1_params_130
0RB---_0LA---_------_------_------,nonhalt,LOOP1_params_130
0RB---_1LA---_------_------_------,halt,LOOP1_params_130
0RB---_1LA0LA_------_------_------,nonhalt,LOOP1_params_130
0RB---_1LA1LA_------_------_------,nonhalt,LOOP1_params_130
0RB---_1LA0RA_------_------_------,nonhalt,LOOP1_params_130
...
```

This step relies on OCaml extraction of the Coq code (specified in `BB5_Extraction.v`).

See `BB5_Extraction/README.md` for more information and troubleshooting.

This extracted `BB5_verified_enumeration.csv` in various compressed formats is also available at [https://docs.bbchallenge.org/CoqBB5_release_v1.0.0/](https://docs.bbchallenge.org/CoqBB5_release_v1.0.0/).

### Results

The proof enumerates **181,385,789** machines, here are the summarized counts (computed from [the CSV extraction](https://docs.bbchallenge.org/CoqBB5_release_v1.0.0/)) of decided machines per decider:

| Decider                            | Nonhalt     | Halt       | Total       |
| -----------------------------------| ----------- | ---------- | ----------- |
| Loops                              | 126,994,099 | 48,379,711 | 175,373,810 |
| n-gram Closed Position Set         | 6,005,142   |            | 6,005,142   |
| Repeated Word List                 | 6,577       |            | 6,577       |
| Halt Max (47,176,870 steps)        | 0           | 183        | 183         |
| Finite Automata Reduction          | 23          |            | 32          |
| Weighted Finite Automata Reduction | 17          |            | 31          |
| Sporadic Machines                  | 13          |            | 13          |
| 1RB reduction ([see below](#table_based-and-normal_form_table_based))                 | 14          |            | 14          |
| Total                              | 133,005,895 | 48,379,894 | 181,385,789 |

Here are more precise counts exactly following the pipeline used by the proof (`BB5_Deciders_Pipeline.v`). Deciders IDs are the same as defined in `BB5_Deciders_Generic.v` which contains parameters information:

| Decider ID                        | Nonhalt     | Halt       | Total       |
| --------------------------------- | ----------- | ---------- | ----------- |
| LOOP1_params_130                  | 126,950,828 | 48,367,435 | 175,318,263 |
| NGRAM_CPS_IMPL2_params_1_1_100    | 3,291,498   |            | 3,291,498   |
| NGRAM_CPS_IMPL2_params_2_2_200    | 1,328,432   |            | 1,328,432   |
| NGRAM_CPS_IMPL2_params_3_3_400    | 497,142     |            | 497,142     |
| NGRAM_CPS_IMPL1_params_2_2_2_1600 | 681,789     |            | 681,789     |
| NGRAM_CPS_IMPL1_params_2_3_3_1600 | 91,101      |            | 91,101      |
| LOOP1_params_4100                 | 43,269      | 12,276     | 55,545      |
| NGRAM_CPS_IMPL1_params_4_2_2_600  | 60,468      |            | 60,468      |
| NGRAM_CPS_IMPL1_params_4_3_3_1600 | 28,868      |            | 28,868      |
| NGRAM_CPS_IMPL1_params_6_2_2_3200 | 16,084      |            | 16,084      |
| NGRAM_CPS_IMPL1_params_6_3_3_3200 | 5,213       |            | 5,213       |
| NGRAM_CPS_IMPL1_params_8_2_2_1600 | 2,279       |            | 2,279       |
| NGRAM_CPS_IMPL1_params_8_3_3_1600 | 855         |            | 855         |
| TABLE_BASED                       | 8,045       | 183        | 8,228       |
| NORMAL_FORM_TABLE_BASED           | 24          |            | 24          |
| Total                             | 133,005,895 | 48,379,894 | 181,385,789 |


#### `TABLE_BASED` and `NORMAL_FORM_TABLE_BASED`

The `TABLE_BASED` ID stands for the machines that were decided using [hardcoded parameters](#generic-vs-hardcoded-parameters) and [Sporadic Machines](#sporadic-machines).

The `NORMAL_FORM_TABLE_BASED` concerns 24 machines whose first transition is `0RB` which are first converted to have `1RB` instead in their first transition (this amounts to simulate the machine until it writes a 1 and then renaming states accordingly), and then decided because the `1RB` version of the machine is listed among the `TABLE_BASED` machines.

Here are decider statistics on `TABLE_BASED` machines:

| Decider/Verifier              | Nonhalt | Halt |
| ----------------------------- | ------- | ---- |
| REP_WL_params_custom          | 6,576   |      |
| NGRAM_CPS_IMPL2_params_custom | 791     |      |
| NGRAM_CPS_IMPL1_params_custom | 216     |      |
| NGRAM_CPS_IMPL1_params_custom | 86      |      |
| NGRAM_CPS_IMPL1_params_custom | 42      |      |
| NGRAM_CPS_IMPL1_params_custom | 26      |      |
| NGRAM_CPS_IMPL1_params_custom | 33      |      |
| NGRAM_CPS_IMPL1_params_custom | 13      |      |
| NGRAM_CPS_IMPL1_params_custom | 20      |      |
| HALT_DECIDER_47176870         | 0       | 183  |
| LOOP1_params_1050000          | 2       |      |
| NGRAM_CPS_LRU_params_custom   | 182     |      |
| NGRAM_CPS_IMPL2_params_custom | 4       |      |
| REP_WL_params_20_2            | 1       |      |
| FAR_certificates              | 23      |      |
| WFAR_certificates             | 17      |      |
| Sporadic Machines             | 13      |      |
| Total                         | 8,045   | 183  |

And on `NORMAL_FORM_TABLE_BASED`:

| NORMAL_FORM_TABLE_BASED    |    |
| -------------------------- | -- |
| FAR                        | 9  |
| WFAR                       | 14 |
| Sporadic Machine (Finned3) | 1  |
|                            | 24 |


## Files index

- `BB5_Deciders_Generic.v`: deciders IDs definition
- `BB5_Deciders_Pipeline.v`: decider pipeline definition and lemmas
- `BB5_Encodings.v`: routines that encode objects into numbers for fast lookup using Coq's `FSets.FMapPositive`
- `BB5_Extraction.v`: OCaml extraction, see [above](#extracting-results)
- `BB5_Make_TM.v`: mainly routines to build 5-state Turing machines
- `BB5_Skelet17.v`: nonhalting proof of machine Skelet's #17 (see [Sporadic Machines](#sporadic-machines) and `BB5_Skelet17.md`)
- `BB5_Sporadic_Machines.v`: collects [Sporadic Machines](#sporadic-machines) proofs
- `BB5_Statement.v`: main definition and `BB(5) = 47,176,870` theorem statement
- `BB5_Theorem.v`: entry point of the proof of `BB(5) = 47,176,870`
- `BB5_TNF_Enumeration.v`: Gathers results from the parallelised Tree Normal Form enumeration (see `BB5_TNF_Enumeration_Roots/`) of 5-state Turing machines
- `BB5_TNF_Enumeration_Roots/`: folder containing the decomposition of the [Tree Normal Form enumeration](#tree-normal-form-tnf-enumeration-parallelised) into several subtrees for parallelisation (one per file starting with prefix `TNF_Root_`). The recursive structure of the folder follows the structure of the tree. 
- `BB5_TNF_Enumeration_Roots/TNF_Roots_Common.v`: defines the root of the TNF tree and its four children, then used by all the files starting with `TNF_Root_`
- `BusyCoq_Translation.v`: translation to tool in order to import [Sporadic Machines](#sporadic-machines) proofs from `../../BusyCoq` (also see the [busycoq repository](https://github.com/meithecatte/busycoq/))

- `List_Routines.v`: routines to manipulate lists
- `List_Tape.v`: routines to manipulate Turing machines tapes as lists
- `Makefile`: allows to build the proof with `make`
- `Prelims.v`: various definitions of general interest
- `Tactics.v`: custom Coq tactics
- `TM.v`: tools to work with Turing Machines
- `TNF.v`: tools for the Tree Normal Form enumeration (e.g. `SearchQueue` implementation etc...)

- `BB5_Extraction/BB5_Extraction.sh`: compiles the OCaml extraction, runs it and saves results to [BB5_verified_enumeration.csv](https://docs.bbchallenge.org/CoqBB5_release_v1.0.0/) (also checks hashes)

- `Deciders/Deciders_Common.v`: common abstraction needed by deciders
- `Deciders/Decider_Halt.v`: decider that detects halting by running a machine for some steps
- `Deciders/Decider_Halt_BB5.v`: Halt Max decider, runs machines up to 47,176,870 steps and detects halting
- `Deciders/Decider_Loop.v`: decider for loops
- `Deciders/Decider_NGramCPS.v`: n-gram Closed Position Set decider
- `Deciders/Decider_RepWL.v`: Repeated Word List decider
- `Deciders/Verifier_Halt.v`: verifier that a machine does halt after a given number of steps
- `Deciders/Verifier_FAR.v`: verifier for Finite Automata Reduction certificates
- `Deciders/Verifier_WFAR.v`: verifier for Weighted Finite Automata Reduction certificates

These deciders are described at length in [bbchallenge's BB5 paper](https://github.com/bbchallenge/bbchallenge-paper), also see `Deciders/README.md` and the comments in each file listed above for some information.

- `BB5_Deciders_Hardcoded_Parameters/`: contains the 8,032 [hardcoded paramaters](#generic-vs-hardcoded-parameters) organised per decider/verifier

[^1]: Removing this axiom would introduce [Setoid](https://coq.inria.fr/doc/v8.9/stdlib/Coq.Setoids.Setoid.html) everywhere.