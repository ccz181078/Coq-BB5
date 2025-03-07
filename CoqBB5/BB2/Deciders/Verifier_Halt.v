From CoqBB2 Require Import Tactics.
From CoqBB2 Require Import BB2_Statement.
From CoqBB2 Require Import List_Tape.
From CoqBB2 Require Import TM.

Definition halt_time_verifier(tm:TM Σ)(n:nat):bool :=
  match ListES_Steps tm n {| List_Tape.l := nil; List_Tape.r := nil; List_Tape.m := Σ0; List_Tape.s := St0 |} with
  | Some {| List_Tape.l:=_; List_Tape.r:=_; List_Tape.m :=m0; List_Tape.s :=s0 |} =>
    match tm s0 m0 with
    | None => true
    | _ => false
    end
  | None => false
  end.

Lemma halt_time_verifier_spec tm n:
  halt_time_verifier tm n = true ->
  HaltsAt _ tm n (InitES Σ Σ0).
Proof.
  unfold halt_time_verifier,HaltsAt.
  intro H.
  pose proof (ListES_Steps_spec tm n {| List_Tape.l := nil; List_Tape.r := nil; List_Tape.m := Σ0; List_Tape.s := St0 |}).
  destruct (ListES_Steps tm n {| List_Tape.l := nil; List_Tape.r := nil; List_Tape.m := Σ0; List_Tape.s := St0 |}).
  2: cg.
  rewrite ListES_toES_O in H0.
  eexists.
  split.
  - apply H0.
  - destruct l as [l0 r0 m0 s0].
    cbn.
    destruct (tm s0 m0); cg.
Qed.