# Coq-BB5

Coq-BB5 (author: [mxdys](https://github.com/ccz181078)) proves theorems in Coq ([v8.20.1](https://github.com/coq/coq/blob/V8.20.1/INSTALL.md)) about [Busy Beaver values](https://wiki.bbchallenge.org/wiki/Main_Page), including the following results:

Original results:
- `BB(5) = 47,176,870`, see [CoqBB5/BB5/](CoqBB5/BB5/)
- `BB(2,4) = 3,932,964`, see [CoqBB5/BB2x4/](CoqBB5/BB2x4/)

Previously known:
- `BB(4) = 107`, see [CoqBB5/BB4/](CoqBB5/BB4/), first proved in [[Brady, 1983]](https://www.ams.org/journals/mcom/1983-40-162/S0025-5718-1983-0689479-6/)
- `BB(3) = 21`, see [CoqBB5/BB3/](CoqBB5/BB3/), first proved in [[Lin, 1963]](https://etd.ohiolink.edu/acprod/odb_etd/etd/r/1501/10?clear=10&p10_accession_num=osu1486554418657614)
- `BB(2) = 6`, see [CoqBB5/BB2/](CoqBB5/BB2/), first proved in [[Radó, 1962]](https://ieeexplore.ieee.org/document/6769603)
- `BB(2,3) = 38`, see [CoqBB5/BB2x3/](CoqBB5/BB2x3/), first proved in [[Lafitte and Papazian, 2007]](https://arxiv.org/pdf/0906.3749)

**Note:** the Coq proofs for the previously known results confirm the results but do not reproduce the original proofs.

**ArXiv preprint:** see our arXiv preprint, which serves as a guide to Coq-BB5: [https://arxiv.org/abs/2509.12337](https://arxiv.org/abs/2509.12337).

## Citing this work

Please cite the following two entries:

```bibtex
@misc{BB5,
      title={{Determination of the fifth Busy Beaver value}}, 
      author={{The bbchallenge Collaboration} and Justin Blanchard and Daniel Briggs and Konrad Deka and Nathan Fenner and Yannick Forster and Georgi Georgiev and Matthew L. House and Rachel Hunter and Iijil and Maja Kądziołka and Pavel Kropitz and Shawn Ligocki and mxdys and Mateusz Naściszewski and savask and Tristan Stérin and Chris Xu and Jason Yuen and Théo Zimmermann},
      year={2025},
      eprint={2509.12337},
      archivePrefix={arXiv},
      primaryClass={cs.LO},
      url={https://arxiv.org/abs/2509.12337}, 
}
```

```bibtex
@software{mxdys_2025_17061968,
  author    = {mxdys},
  title     = {{Coq-BB5 release v1.0.0}},
  month     = sep,
  year      = 2025,
  publisher = {Zenodo},
  version   = {1.0.0},
  doi       = {10.5281/zenodo.17061968},
  url       = {https://doi.org/10.5281/zenodo.17061968},
  note      = {\url{https://doi.org/10.5281/zenodo.17061968}}
}
```


## Structure of the proofs

The [proof of BB(5)](CoqBB5/BB5/) is the most general one in the sense that:

1. All the other proofs only use subsets of the techniques used to prove BB(5).
2. All the other proofs use the same overall [structure as the BB(4) proof](CoqBB5/BB4/README.md#proof-structure), which is itself a slight simplification of the [structure of the BB(5) proof](CoqBB5/BB5/README.md#proof-structure).

## BusyCoq

For the proof of `BB(5) = 47,176,870`, Coq-BB5 relies on the [busycoq](https://github.com/meithecatte/busycoq/tree/333695b79707189d49f5e560a55c3ab8dda1cdc6) library (author: [meithecatte](https://github.com/meithecatte)) for proving that some individual 5-state 2-symbol Turing machines, called [Sporadic Machines](CoqBB5/BB5/README.md#sporadic-machines), do not halt. The `BusyCoq/` folder contains a partial snapshot of `busycoq`, i.e. only the proofs that are used in `CoqBB5/BB5/`.
