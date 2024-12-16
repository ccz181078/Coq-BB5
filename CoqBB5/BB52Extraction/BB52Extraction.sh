cp printers.out printers.ml
cp bb5_verified_enumeration.out bb5_verified_enumeration.ml
ulimit -s unlimited
ocamlbuild bb5_verified_enumeration.native -pkg zarith
