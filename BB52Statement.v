Require Import ZArith.

Inductive St:Set :=
| St0
| St1
| St2
| St3
| St4.

Inductive Σ:Set :=
| Σ0
| Σ1.

Inductive Dir:Set :=
| Dneg
| Dpos.

Definition Dir_to_Z(x:Dir) :=
match x with
| Dneg => Zneg 1
| Dpos => Zpos 1
end.

Section TM.

Hypothesis Σ:Set.
Hypothesis Σ0:Σ.

Record Trans:Set := {
  nxt: St;
  dir: Dir;
  out: Σ;
}.

Definition TM:Set := St->Σ->option Trans.

Definition ExecState:Set := St*(Z->Σ).

Definition InitES:ExecState := (St0,fun _=>Σ0).

Definition upd(t:(Z->Σ))(o:Σ) :=
  fun x:Z => if Z.eqb x Z0 then o else t x.

Definition mov(t:(Z->Σ))(d:Dir) :=
  fun x:Z => t ((x+(Dir_to_Z d))%Z).

Definition step(tm:TM)(st:ExecState): option ExecState :=
  let (s,t):=st in
  match tm s (t Z0) with
  | None => None
  | Some tr =>
    let (s',d,o):=tr in
    Some (s',mov (upd t o) d)
  end.

Inductive Steps: TM->nat->ExecState->ExecState->Prop :=
| steps_O tm st:
  Steps tm O st st
| steps_S tm n st st0 st1:
  Steps tm n st st0 ->
  step tm st0 = Some st1 ->
  Steps tm (S n) st st1.

Inductive HaltsAt(tm:TM): nat->ExecState->Prop :=
| HaltsAt_intro n st:
  (exists st', Steps tm n st st' /\ step tm st' = None) ->
  HaltsAt tm (S n) st.

End TM.

Definition BB5 := 47176870%N.

Definition BB5_value_statement :=
  (forall tm n0, HaltsAt Σ tm n0 (InitES Σ Σ0) -> n0 <= N.to_nat BB5) /\
  (exists tm, HaltsAt Σ tm (N.to_nat BB5) (InitES Σ Σ0)).

