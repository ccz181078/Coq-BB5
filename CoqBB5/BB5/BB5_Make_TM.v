Require Import ZArith.
Require Import Lia.
Require Import List.

From CoqBB5 Require Import BB5_Statement.
From CoqBB5 Require Import TM.
From CoqBB5 Require Import List_Routines.
From CoqBB5 Require Import Tactics.
From CoqBB5 Require Import Prelims.
From CoqBB5 Require Import BB5_Encodings.


Definition AL0 := Some {| nxt:=St0; dir:=Dneg; out:=Σ0 |}.
Definition AL1 := Some {| nxt:=St0; dir:=Dneg; out:=Σ1 |}.
Definition AR0 := Some {| nxt:=St0; dir:=Dpos; out:=Σ0 |}.
Definition AR1 := Some {| nxt:=St0; dir:=Dpos; out:=Σ1 |}.

Definition BL0 := Some {| nxt:=St1; dir:=Dneg; out:=Σ0 |}.
Definition BL1 := Some {| nxt:=St1; dir:=Dneg; out:=Σ1 |}.
Definition BR0 := Some {| nxt:=St1; dir:=Dpos; out:=Σ0 |}.
Definition BR1 := Some {| nxt:=St1; dir:=Dpos; out:=Σ1 |}.

Definition CL0 := Some {| nxt:=St2; dir:=Dneg; out:=Σ0 |}.
Definition CL1 := Some {| nxt:=St2; dir:=Dneg; out:=Σ1 |}.
Definition CR0 := Some {| nxt:=St2; dir:=Dpos; out:=Σ0 |}.
Definition CR1 := Some {| nxt:=St2; dir:=Dpos; out:=Σ1 |}.

Definition DL0 := Some {| nxt:=St3; dir:=Dneg; out:=Σ0 |}.
Definition DL1 := Some {| nxt:=St3; dir:=Dneg; out:=Σ1 |}.
Definition DR0 := Some {| nxt:=St3; dir:=Dpos; out:=Σ0 |}.
Definition DR1 := Some {| nxt:=St3; dir:=Dpos; out:=Σ1 |}.

Definition EL0 := Some {| nxt:=St4; dir:=Dneg; out:=Σ0 |}.
Definition EL1 := Some {| nxt:=St4; dir:=Dneg; out:=Σ1 |}.
Definition ER0 := Some {| nxt:=St4; dir:=Dpos; out:=Σ0 |}.
Definition ER1 := Some {| nxt:=St4; dir:=Dpos; out:=Σ1 |}.

Definition HL0:option (Trans Σ) := None.
Definition HL1:option (Trans Σ) := None.
Definition HR0:option (Trans Σ) := None.
Definition HR1:option (Trans Σ) := None.

Definition makeTM:
(option (Trans Σ))->(option (Trans Σ))->
(option (Trans Σ))->(option (Trans Σ))->
(option (Trans Σ))->(option (Trans Σ))->
(option (Trans Σ))->(option (Trans Σ))->
(option (Trans Σ))->(option (Trans Σ))->
(TM Σ) :=
fun A0 A1 B0 B1 C0 C1 D0 D1 E0 E1 s i =>
match s,i with
| St0,Σ0 => A0
| St0,Σ1 => A1
| St1,Σ0 => B0
| St1,Σ1 => B1
| St2,Σ0 => C0
| St2,Σ1 => C1
| St3,Σ0 => D0
| St3,Σ1 => D1
| St4,Σ0 => E0
| St4,Σ1 => E1
end.

Definition Trans_list:=
{| nxt:=St0; dir:=Dneg; out:=Σ0 |}::
{| nxt:=St0; dir:=Dneg; out:=Σ1 |}::
{| nxt:=St0; dir:=Dpos; out:=Σ0 |}::
{| nxt:=St0; dir:=Dpos; out:=Σ1 |}::
{| nxt:=St1; dir:=Dneg; out:=Σ0 |}::
{| nxt:=St1; dir:=Dneg; out:=Σ1 |}::
{| nxt:=St1; dir:=Dpos; out:=Σ0 |}::
{| nxt:=St1; dir:=Dpos; out:=Σ1 |}::
{| nxt:=St2; dir:=Dneg; out:=Σ0 |}::
{| nxt:=St2; dir:=Dneg; out:=Σ1 |}::
{| nxt:=St2; dir:=Dpos; out:=Σ0 |}::
{| nxt:=St2; dir:=Dpos; out:=Σ1 |}::
{| nxt:=St3; dir:=Dneg; out:=Σ0 |}::
{| nxt:=St3; dir:=Dneg; out:=Σ1 |}::
{| nxt:=St3; dir:=Dpos; out:=Σ0 |}::
{| nxt:=St3; dir:=Dpos; out:=Σ1 |}::
{| nxt:=St4; dir:=Dneg; out:=Σ0 |}::
{| nxt:=St4; dir:=Dneg; out:=Σ1 |}::
{| nxt:=St4; dir:=Dpos; out:=Σ0 |}::
{| nxt:=St4; dir:=Dpos; out:=Σ1 |}::
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
  | Σ0 => (listStΣ_enc x1)~0
  | Σ1 => (listStΣ_enc x1)~1
  end.

Lemma Σ_history_enc_inj: is_inj Σ_history_enc.
Proof.
  intros x1 x2 H.
  destruct x1 as [a1 b1].
  destruct x2 as [a2 b2].
  cbn in H.
  destruct a1,a2; invst H; f_equal; apply listStΣ_enc_inj,H1.
Qed.

Definition TM_enc(tm:TM Σ):positive :=
  match TM_to_N tm with
  | N0 => xH
  | Npos v => Pos.succ v
  end.

Definition TM_simplify tm :=
  makeTM
  (tm St0 Σ0) (tm St0 Σ1)
  (tm St1 Σ0) (tm St1 Σ1)
  (tm St2 Σ0) (tm St2 Σ1)
  (tm St3 Σ0) (tm St3 Σ1)
  (tm St4 Σ0) (tm St4 Σ1).

Lemma TM_simplify_spec tm:
  TM_simplify tm = tm.
Proof.
  unfold TM_simplify,makeTM.
  fext. fext.
  destruct x,x0; reflexivity.
Qed.