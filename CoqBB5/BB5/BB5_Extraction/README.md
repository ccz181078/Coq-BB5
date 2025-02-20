# BB5 Extraction

First compile the BB5 proof, see `../README.md`. This will generate `BB5_verified_enumeration.out` and `printers.out` which are OCaml files.

### OCaml setup

Compiling the BB5 extraction with OCaml 5 has proven less prone to compiler stack overflows than with OCaml 4 (which is used to compile the proof, see `../README.md`). Using [opam](https://opam.ocaml.org/doc/Install.html), run the following: 

```
opam switch 5.1.1
eval $(opam env)
opam install ocamlbuild ocamlfind zarith
```

### Compile and run the extraction

Then, run `./BB5_Extraction.sh`.

This script will:

1. Compile the OCaml files. **Warning:** you may need to increase the size of your stack (e.g. `ulimit -s unlimited`) for this step.
2. Create `BB5_verified_enumeration.csv` with headers
3. Run the compiled OCaml program which will run the Tree Normal Form enumeration and deciders (see `../README.md`) and appends outputs to `BB5_verified_enumeration.csv`
4. Remove the trailing empty line at the end of `BB5_verified_enumeration.csv`
5. Check that the generated file has the expected hash

Results of this extraction are discussed in `../README.md`.