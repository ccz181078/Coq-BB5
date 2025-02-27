# BB3 Extraction

First compile the BB3 proof, see `../README.md`. This will generate `BB3_verified_enumeration.out` and `printers.out` which are OCaml files.

Then, make sure you have the following OCaml packages:

```
opam install ocamlbuild
opam install ocamlfind
opam install zarith
```

Then, run `./BB3_Extraction.sh`.

This script will:

1. Compile the OCaml files. **Warning:** you may need to increase the size of your stack (e.g. `ulimit -s unlimited`) for this step.
2. Create `BB3_verified_enumeration.csv` with headers
3. Run the compiled OCaml program which will run the Tree Normal Form enumeration and deciders (see `../README.md`) and appends outputs to `BB3_verified_enumeration.csv`
4. Remove the trailing empty line at the end of `BB3_verified_enumeration.csv`
5. Check that the generated file has the expected hash

Results of this extraction are discussed in `../README.md`.