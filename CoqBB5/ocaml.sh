mv printers.out printers.ml
mv code.out code.ml
ulimit -s unlimited
ocamlbuild code.native -pkg zarith
