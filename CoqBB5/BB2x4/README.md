# BB(2,4) = 3,932,964

This folder contains the Coq (v8.20.1) proof that `BB(2,4) = 3,932,964`. This result means that the maximum number of steps that a halting 2-state 4-symbol Turing machine can do from all-0 tape is 3,932,964. 

Proving this results involves enumerating 2-state 4-symbol Turing machines and decide for each whether it halts or not and, if it halts, that it halts after at most 3,932,964 steps.

The [extracted results](#extracting-results) from these proof are available at [https://docs.bbchallenge.org/CoqBB5_release_v0.9.0/](https://docs.bbchallenge.org/CoqBB5_release_v0.9.0/) in the form of a CSV file, `BB2x4_verified_enumeration.csv` listing each enumerated machine with its halting status (halt/nonhalt) as well as the ID of the decider that decided it (IDs as defined in `BB2x4_Deciders_Generic.v`).

## Compile the proof

In order to compile the proof (assuming you have Coq v8.20.1 installed), do:

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
- n-gram Closed Position Set (n-gram CPS), see `../BB5/Deciders/Decider_NGramCPS.v`
- Repeated Word List (RepWL), see `../BB5/Deciders/Decider_RepWL.v`
- Halt Max (run machines up to 3,932,964 steps), see `Deciders/Decider_Halt_BB2x4.v`

Each of these techniques is described in [bbchallenge's BB5 paper](https://github.com/bbchallenge/bbchallenge-paper).

The deciders' algorithms are programmed in Coq and then proved correct in Coq too (i.e. proving that if they output `HALT`/`NONHALT` on a machine then the machine halts/does not halt).

### Extracting results

The list of all enumerated machines (using [bbchallenge format](https://discuss.bbchallenge.org/t/standard-tm-text-format/60/28?u=cosmo)) with for each, halting status and decider ID can be extracted from the Coq proof by doing (once you've compiled the proof):

```
cd BB2x4_Extraction
./BB2x4_Extraction.sh
```

Which should produce the file `BB2x4_verified_enumeration.csv` with shasum ending in `...dbbe59a814` and file starting with:

```
machine,status,decider
------------_------------,halt,LOOP1_params_107
0RA---------_------------,nonhalt,LOOP1_params_107
1RA---------_------------,nonhalt,LOOP1_params_107
2RA---------_------------,nonhalt,LOOP1_params_107
3RA---------_------------,nonhalt,LOOP1_params_107
0RB---------_------------,halt,LOOP1_params_107
0RB---------_0LA---------,nonhalt,LOOP1_params_107
0RB---------_1LA---------,halt,LOOP1_params_107
0RB---------_1LA0LA------,nonhalt,LOOP1_params_107
...
```

This step relies on OCaml extraction of the Coq code (specified in `BB2x4_Extraction.v`).

See `BB2x4_Extraction/README.md` for more information and troubleshooting.

This extracted `BB2x4_verified_enumeration.csv` is also available at [https://docs.bbchallenge.org/CoqBB5_release_v0.9.0/](https://docs.bbchallenge.org/CoqBB5_release_v0.9.0/).

### Results

The proof enumerates **2,154,217** machines, here are summarized counts of decided machines per decider:

| Decider                        | Nonhalt   | Halt    | Total     |
| ------------------------------ | --------- | ------- | --------- |
| Loops                          | 1,263,302 | 721,313 | 1,984,615 |
| n-gram Closed Position Set     | 163,500   | 0       | 163,500   |
| Repeated Word List             | 6,078     | 0       | 6,078     |
| Halt Max (3,932,964 steps)     | 0         | 24      | 24        |
|                                | 1,432,880 | 721,337 | 2,154,217 |

Here are more precise counts following exactly the pipeline (and deciders ID, see `BB2x4_Deciders_Generic.v`) used by the proof (`BB2x4_Deciders_Pipeline.v`), with parameters for each method:

|                                   | Nonhalt   | Halt    | Total     |
| --------------------------------- | --------- | ------- | --------- |
| LOOP1_params_107                  | 1,262,432 | 720,959 | 1,983,391 |
| NGRAM_CPS_IMPL2_params_1_1_400    | 102,018   |         |           |
| NGRAM_CPS_IMPL2_params_2_2_800    | 49,224    |         |           |
| NGRAM_CPS_IMPL2_params_3_3_400    | 7,518     |         |           |
| NGRAM_CPS_IMPL2_params_4_4_800    | 2,286     |         |           |
| LOOP1_params_4100                 | 870       | 354     | 1,224     |
| REPWL_2_3_320_400                 | 6,012     |         |           |
| NGRAM_CPS_LRU_params_2_2_1000     | 1,206     |         |           |
| NGRAM_CPS_IMPL1_params_2_2_2_3000 | 894       |         |           |
| NGRAM_CPS_IMPL1_params_2_3_3_1600 | 120       |         |           |
| NGRAM_CPS_IMPL1_params_4_2_2_600  | 12        |         |           |
| NGRAM_CPS_IMPL1_params_4_3_3_1600 | 90        |         |           |
| NGRAM_CPS_IMPL1_params_6_2_2_3200 | 48        |         |           |
| NGRAM_CPS_IMPL1_params_6_3_3_3200 | 36        |         |           |
| NGRAM_CPS_IMPL1_params_8_3_3_1600 | 6         |         |           |
| NGRAM_CPS_LRU_params_3_3_20000    | 24        |         |           |
| REPWL_params_4_2_320_2000         | 54        |         |           |
| REPWL_params_6_2_320_2000         | 12        |         |           |
| NGRAM_CPS_IMPL2_params_4_4_20000  | 18        |         |           |
| HALT_MAX_params_3932964           | 0         | 24      |           |
| Total                             | 1,432,880 | 721,337 | 2,154,217 |