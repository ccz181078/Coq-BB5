From BusyCoq Require Export Individual BB52.

Module Individual52 := Individual BB52.
Export Individual52.

Declare Scope sym_scope.
Bind Scope sym_scope with Sym.
Delimit Scope sym_scope with sym.
Open Scope sym.

Notation "0" := S0 : sym_scope.
Notation "1" := S1 : sym_scope.

(* Make sure that [{{D}}>] still refers to the state, even if we shadowed
   [D] itself with something else. *)
Notation "l '{{A}}>'  r" := (l {{A}}> r) (at level 30).
Notation "l '{{B}}>'  r" := (l {{B}}> r) (at level 30).
Notation "l '{{C}}>'  r" := (l {{C}}> r) (at level 30).
Notation "l '{{D}}>'  r" := (l {{D}}> r) (at level 30).
Notation "l '{{E}}>'  r" := (l {{E}}> r) (at level 30).

Notation "l '<{{A}}' r" := (l <{{A}} r) (at level 30).
Notation "l '<{{B}}' r" := (l <{{B}} r) (at level 30).
Notation "l '<{{C}}' r" := (l <{{C}} r) (at level 30).
Notation "l '<{{D}}' r" := (l <{{D}} r) (at level 30).
Notation "l '<{{E}}' r" := (l <{{E}} r) (at level 30).
