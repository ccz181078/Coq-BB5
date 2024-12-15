# OCaml extraction of the bb5 enumeration

Coq-BB5 extracts an OCaml program (see ../BB52Extraction.v) named `bb5_enumeration.out` which prints all the enumerated Turing machines with their proved halting status from blank tape (halt or nonhalt). To run the program, do:

```
chmod +x BB52Extraction.sh
./BB52Extraction.sh
./bb5_enumeration.native
```

**NOTE:** compilation of the generated OCaml files can stack overflow which is why the script contains `ulimit -s unlimited` to increase the stack size of your current shell, but you may need to run the script as sudo to execute that command. 

Once compiled, launch the Coq-verified enumeration with:

`./bb5_enumeration.native` and you should see each enumerated machine and its proved halting status:

```
------_------_------_------_------,halt
0RA---_------_------_------_------,nonhalt
1RA---_------_------_------_------,nonhalt
0RB---_------_------_------_------,halt
0RB---_0LA---_------_------_------,nonhalt
0RB---_1LA---_------_------_------,halt
0RB---_1LA0LA_------_------_------,nonhalt
0RB---_1LA1LA_------_------_------,nonhalt
0RB---_1LA0RA_------_------_------,nonhalt
0RB---_1LA1RA_------_------_------,nonhalt
...
```

The total enumeration contains 181,385,789 machines and is about 7Gb.
