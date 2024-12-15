cp printers.out printers.ml
cp bb5_enumeration.out bb5_enumeration.ml
ulimit -s unlimited
ocamlbuild bb5_enumeration.native -pkg zarith
