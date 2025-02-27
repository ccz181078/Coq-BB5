# BB(3) = 21

This folder contains the Coq ([v8.20.1](https://github.com/coq/coq/blob/V8.20.1/INSTALL.md)) proof that `BB(3) = 21`. This result was first proved, in [[Lin, 1963]](https://etd.ohiolink.edu/acprod/odb_etd/etd/r/1501/10?clear=10&p10_accession_num=osu1486554418657614).

This result means that the maximum number of steps that a halting 3-state Turing machine can do from all-0 tape is 21. See [bbchallenge's wiki](https://wiki.bbchallenge.org/wiki/Main_Page) or [bbchallenge's BB5 paper](https://github.com/bbchallenge/bbchallenge-paper) for more background and detailed information.

Proving this results involves enumerating 3-state Turing machines and deciding for each whether it halts or not and, if it halts, that it halts in at most 21 steps.

The extracted data from this proof is available at [https://docs.bbchallenge.org/CoqBB5_release_v1.0.0/BB3_verified_enumeration.csv](https://docs.bbchallenge.org/CoqBB5_release_v1.0.0/BB3_verified_enumeration.csv) in the form of a CSV file listing each enumerated machine with its halting status (halt/nonhalt) as well as the ID of the decider that decided it (IDs as defined in `BB3_Deciders_Generic.v`). More details [below](#extracting-results).

## Compiling the proof

Assuming you have [opam installed](https://opam.ocaml.org/doc/Install.html), you can install Coq v8.20.1 using:

```
opam switch create 4.14.2 # if already existent do: opam switch 4.14.2
eval $(opam env)
opam install coq-native
opam pin add coq 8.20.1
```

Then, in order to compile the proof, do:

```
./create_proof_files.sh
make
```

#### Compile time 

Compiling the proof takes about 30 seconds (Apple silicon), using `coq-native`.

### Used Axiom

As outputted at the end of the compilation, the proof only depends on Coq's standard library axiom [functional_extensionality_dep](https://coq.inria.fr/doc/v8.9/stdlib/Coq.Logic.FunctionalExtensionality.html):

```
functional_extensionality_dep
  : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
    (forall x : A, f x = g x) -> f = g
```

This axiom is used to simplify the equality between `TM` and `ExecState` (both defined in `BB3_Statement.v`) since they are represented by functions[^2]. 

## Proof structure

The main definitions and `BB(3) = 21` theorem statement are in `BB3_Statement.v` (this file does not require much Coq knowledge to be understood). The entry-point of the proof is located in `BB3_Theorem.v`.

### Tree Normal Form (TNF) enumeration

The proof enumerates 3-state machines in [Tree Normal Form](https://wiki.bbchallenge.org/wiki/Tree_Normal_Form) (**TNF**). Each enumerated machine is passed through a pipeline of deciders which are algorithm trying to prove whether the machine halts or not:

- If the machine halts, i.e. meets an undefined transition, a new subtree of machines is visited for all the possible ways to fill the undefined transition
- If the machine does not halt, it is a leaf of the TNF tree

The TNF enumeration terminates when all leafs have been reached, i.e. all the enumerated Turing machines have been decided and there are no more halting machines to expand into subtrees.

The TNF enumeration algorithm is located in `BB3_TNF_Enumeration.v`.

**Technicalities:** the implemented TNF enumeration safely ignores machines whose first head move direction is `Left` since they can be symmetrised to use `Right` instead. However, contrarily to other implementations (such as [TNF-1RB](https://wiki.bbchallenge.org/wiki/Tree_Normal_Form#TNF-1RB)), this enumeration contains both machines that start by writing a `0` and those that start by writing a `1`, yielding a bigger search space but a simpler proof.  

### Deciders

Deciders are algorithms trying to prove whether a given Turing machine halts or not. The pipeline of deciders used to solve `BB(4)` (pipeline defined in `BB3_Deciders_Pipeline.v`) is a subset of the `BB(5)` pipeline (see ../BB5):

1. Loops, see `../BB5/Deciders/Decider_Loop.v`
2. n-gram Closed Position Set (n-gram CPS), see `../BB5/Deciders/Decider_NGramCPS.v`
3. Repeated Word List (RepWL), see `../BB5/Deciders/Decider_RepWL.v`

Each of these techniques is described at length in [bbchallenge's BB5 paper](https://github.com/bbchallenge/bbchallenge-paper), also see `../BB5/Deciders/README.md` and the comments in each file listed above for some information.

The deciders' algorithms are programmed in Coq and then proved correct in Coq too (i.e. proving that if they output `HALT`/`NONHALT` on a machine then the machine halts/does not halt).

### Extracting results

The list of all enumerated machines (using [bbchallenge format](https://discuss.bbchallenge.org/t/standard-tm-text-format/60/28?u=cosmo)) with for each, halting status and decider ID can be extracted from the Coq proof by doing (once you've compiled the proof):

```
cd BB3_Extraction
./BB3_Extraction.sh
```

Which should produce the file `BB3_verified_enumeration.csv` with shasum ending in `...3fc021f27` and file starting with:

```
machine,status,decider
------_------_------,halt,LOOP1_params_21
0RA---_------_------,nonhalt,LOOP1_params_21
1RA---_------_------,nonhalt,LOOP1_params_21
0RB---_------_------,halt,LOOP1_params_21
0RB---_0LA---_------,nonhalt,LOOP1_params_21
0RB---_1LA---_------,halt,LOOP1_params_21
0RB---_1LA0LA_------,nonhalt,LOOP1_params_21
0RB---_1LA1LA_------,nonhalt,LOOP1_params_21
0RB---_1LA0RA_------,nonhalt,LOOP1_params_21
...
```

This step relies on OCaml extraction of the Coq code (specified in `BB3_Extraction.v`).

See `BB3_Extraction/README.md` for more information and troubleshooting.

This extracted `BB3_verified_enumeration.csv` is also available at [https://docs.bbchallenge.org/CoqBB5_release_v1.0.0/](https://docs.bbchallenge.org/CoqBB5_release_v1.0.0/).

### Results

The proof enumerates **5,417** machines, here are the summarized counts (computed from [the CSV extraction](https://docs.bbchallenge.org/CoqBB5_release_v1.0.0/BB3_verified_enumeration.csv)) of decided machines per decider:

TODO



## Files index

- `_BB3_Legacy_Monolith.v`: original monolithic proof of `BB(4) = 107`, without extraction

- `create_proof_files.sh`: copies and does some renaming on files imported from `../BB5`, also creates `Makefile` and `_CoqProject`
- `BB3_Deciders_Generic.v`: deciders IDs definition
- `BB3_Deciders_Pipeline.v`: decider pipeline definition and lemmas
- `BB3_Encodings.v`: routines that encode objects into numbers for fast lookup using Coq's `FSets.FMapPositive`
- `BB3_Extraction.v`: OCaml extraction, see [above](#extracting-results)
- `BB3_Make_TM.v`: mainly routines to build 3-state Turing machines
- `BB3_Statement.v`: main definition and `BB(4) = 107` theorem statement
- `BB3_Theorem.v`: entry point of the proof of `BB(4) = 107`
- `BB3_TNF_Enumeration.v`: Tree Normal Form enumeration of 3-state Turing machines
- `BB3_Extraction/BB3_Extraction.sh`: compiles the OCaml extraction, runs it and saves results to [BB3_verified_enumeration.csv](https://docs.bbchallenge.org/CoqBB5_release_v1.0.0/) (also checks hashes)

Files imported from `../BB5` after running `create_proof_files.sh`:

- `Makefile`: allows to build the proof with `make`
- `List_Routines.v`: routines to manipulate lists
- `List_Tape.v`: routines to manipulate Turing machines tapes as lists
- `Prelims.v`: various definitions of general interest
- `Tactics.v`: custom Coq tactics
- `TM.v`: tools to work with Turing Machines
- `TNF.v`: tools for the Tree Normal Form enumeration (e.g. `SearchQueue` implementation etc...)

- `Deciders/Deciders_Common.v`: common abstraction needed by deciders
- `Deciders/Decider_Halt.v`: decider that detects halting by running a machine for some steps
- `Deciders/Decider_Loop.v`: decider for loops
- `Deciders/Decider_NGramCPS.v`: n-gram Closed Position Set decider
- `Deciders/Decider_RepWL.v`: Repeated Word List decider
- `Deciders/Verifier_Halt.v`: verifier that a machine does halt after a given number of steps

These deciders are described at length in [bbchallenge's BB5 paper](https://github.com/bbchallenge/bbchallenge-paper), also see `../BB5/Deciders/README.md` and the comments in each file listed above for some information.

[^1]: Quoting the paper: "All of the remaining holdouts were examined by means of voluminous printouts of their histories along with some program extracted features. It was determined to the author's satisfaction that none of these machines will ever stop." 
[^2]: Removing this axiom would introduce [Setoid](https://coq.inria.fr/doc/v8.9/stdlib/Coq.Setoids.Setoid.html) everywhere.