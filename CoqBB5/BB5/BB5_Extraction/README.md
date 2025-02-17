# OCaml extraction of the bb5 enumeration

OCaml packages you need: 

```
opam install ocamlbuild
opam install ocamlfind
opam install zarit
```

Coq-BB5 extracts an OCaml program (see ../BB52Extraction.v) named `bb5_verified_enumeration.out` which prints all the enumerated Turing machines with their proved halting status from blank tape (halt or nonhalt) and decider. To run the program, do:

```
chmod +x BB52Extraction.sh
./BB52Extraction.sh
./bb5_verified_enumeration.native
```

**NOTE:** compilation of the generated OCaml files can stack overflow which is why the script contains `ulimit -s unlimited` to increase the stack size of your current shell, but you may need to run the script as sudo to execute that command. 

Once compiled, launch the Coq-verified enumeration with:

`./bb5_verified_enumeration.native` and you should see each enumerated machine and its proved halting status:

```
machine,status,decider
------_------_------_------_------,halt,LOOP1_params_130_512
0RA---_------_------_------_------,nonhalt,LOOP1_params_130_512
1RA---_------_------_------_------,nonhalt,LOOP1_params_130_512
0RB---_------_------_------_------,halt,LOOP1_params_130_512
0RB---_0LA---_------_------_------,nonhalt,LOOP1_params_130_512
0RB---_1LA---_------_------_------,halt,LOOP1_params_130_512
0RB---_1LA0LA_------_------_------,nonhalt,LOOP1_params_130_512
0RB---_1LA1LA_------_------_------,nonhalt,LOOP1_params_130_512
0RB---_1LA0RA_------_------_------,nonhalt,LOOP1_params_130_512
...
```

The total enumeration contains 181,385,789 machines and is about 7Gb.
