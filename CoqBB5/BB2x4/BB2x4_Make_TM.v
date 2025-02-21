Require Import ZArith.
Require Import Lia.
Require Import List.

From CoqBB2x4 Require Import BB2x4_Statement.
From CoqBB2x4 Require Import TM.
From CoqBB2x4 Require Import List_Routines.
From CoqBB2x4 Require Import Tactics.
From CoqBB2x4 Require Import Prelims.
From CoqBB2x4 Require Import BB2x4_Encodings.


Definition AL0 := Some {| nxt:=St0; dir:=Dneg; out:=Σ0 |}.
Definition AL1 := Some {| nxt:=St0; dir:=Dneg; out:=Σ1 |}.
Definition AL2 := Some {| nxt:=St0; dir:=Dneg; out:=Σ2 |}.
Definition AL3 := Some {| nxt:=St0; dir:=Dneg; out:=Σ3 |}.
Definition AR0 := Some {| nxt:=St0; dir:=Dpos; out:=Σ0 |}.
Definition AR1 := Some {| nxt:=St0; dir:=Dpos; out:=Σ1 |}.
Definition AR2 := Some {| nxt:=St0; dir:=Dpos; out:=Σ2 |}.
Definition AR3 := Some {| nxt:=St0; dir:=Dpos; out:=Σ3 |}.

Definition BL0 := Some {| nxt:=St1; dir:=Dneg; out:=Σ0 |}.
Definition BL1 := Some {| nxt:=St1; dir:=Dneg; out:=Σ1 |}.
Definition BL2 := Some {| nxt:=St1; dir:=Dneg; out:=Σ2 |}.
Definition BL3 := Some {| nxt:=St1; dir:=Dneg; out:=Σ3 |}.
Definition BR0 := Some {| nxt:=St1; dir:=Dpos; out:=Σ0 |}.
Definition BR1 := Some {| nxt:=St1; dir:=Dpos; out:=Σ1 |}.
Definition BR2 := Some {| nxt:=St1; dir:=Dpos; out:=Σ2 |}.
Definition BR3 := Some {| nxt:=St1; dir:=Dpos; out:=Σ3 |}.

Definition HR1:option (Trans Σ) := None.

Definition makeTM:
(option (Trans Σ))->(option (Trans Σ))->
(option (Trans Σ))->(option (Trans Σ))->
(option (Trans Σ))->(option (Trans Σ))->
(option (Trans Σ))->(option (Trans Σ))->
(TM Σ) :=
fun A0 A1 A2 A3 B0 B1 B2 B3 s i =>
match s,i with
| St0,Σ0 => A0
| St0,Σ1 => A1
| St0,Σ2 => A2
| St0,Σ3 => A3
| St1,Σ0 => B0
| St1,Σ1 => B1
| St1,Σ2 => B2
| St1,Σ3 => B3
end.

Definition Trans_list:=
{| nxt:=St0; dir:=Dneg; out:=Σ0 |}::
{| nxt:=St0; dir:=Dneg; out:=Σ1 |}::
{| nxt:=St0; dir:=Dneg; out:=Σ2 |}::
{| nxt:=St0; dir:=Dneg; out:=Σ3 |}::
{| nxt:=St0; dir:=Dpos; out:=Σ0 |}::
{| nxt:=St0; dir:=Dpos; out:=Σ1 |}::
{| nxt:=St0; dir:=Dpos; out:=Σ2 |}::
{| nxt:=St0; dir:=Dpos; out:=Σ3 |}::
{| nxt:=St1; dir:=Dneg; out:=Σ0 |}::
{| nxt:=St1; dir:=Dneg; out:=Σ1 |}::
{| nxt:=St1; dir:=Dneg; out:=Σ2 |}::
{| nxt:=St1; dir:=Dneg; out:=Σ3 |}::
{| nxt:=St1; dir:=Dpos; out:=Σ0 |}::
{| nxt:=St1; dir:=Dpos; out:=Σ1 |}::
{| nxt:=St1; dir:=Dpos; out:=Σ2 |}::
{| nxt:=St1; dir:=Dpos; out:=Σ3 |}::
nil.

Lemma Trans_list_spec:
  forall tr, In tr Trans_list.
Proof.
  intro.
  destruct tr as [s d o].
  cbn.
  destruct s,d,o; tauto.
Qed.

Definition Σ_history_enc(x:Σ_history):positive:=
  let (x0,x1):=x in
  match x0 with
  | Σ0 => (listStΣ_enc x1)~0~0
  | Σ1 => (listStΣ_enc x1)~1~0
  | Σ2 => (listStΣ_enc x1)~0~1
  | Σ3 => (listStΣ_enc x1)~1~1
  end.

Lemma Σ_history_enc_inj: is_inj Σ_history_enc.
Proof.
  intros x1 x2 H.
  destruct x1 as [a1 b1].
  destruct x2 as [a2 b2].
  cbn in H.
  destruct a1,a2; invst H; f_equal; apply listStΣ_enc_inj,H1.
Qed.

Definition TM_simplify tm :=
  makeTM
  (tm St0 Σ0) (tm St0 Σ1) (tm St0 Σ2) (tm St0 Σ3)
  (tm St1 Σ0) (tm St1 Σ1) (tm St1 Σ2) (tm St1 Σ3).

Lemma TM_simplify_spec tm:
  TM_simplify tm = tm.
Proof.
  unfold TM_simplify,makeTM.
  fext. fext.
  destruct x,x0; reflexivity.
Qed.