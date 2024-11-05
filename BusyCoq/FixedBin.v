(** * Fixed-width binary words *)

From Coq Require Import Lia.
From Coq Require Import PArith.BinPos PArith.Pnat.
From Coq Require Import NArith.BinNat NArith.Nnat.
From BusyCoq Require Import Helper.
Set Default Goal Selector "!".

Inductive bin : nat -> Type :=
  | bb : bin 0
  | b0 {k} : bin k -> bin (S k)
  | b1 {k} : bin k -> bin (S k).

Reserved Notation "c -S-> c'" (at level 40, c' at next level).

Inductive bin_succ : forall {k}, bin k -> bin k -> Prop :=
  | succ_b0 {k} (n : bin k)    : (b0 n) -S-> (b1 n)
  | succ_b1 {k} (n n' : bin k) : n -S-> n'  ->  b1 n -S-> b0 n'

  where "c -S-> c'" := (bin_succ c c').

Inductive bin_plus {k} : N -> bin k -> bin k -> Prop :=
  | plus_0 n : bin_plus N0 n n
  | plus_S u n n' n'' :
    n -S-> n' ->
    bin_plus         u  n' n'' ->
    bin_plus (N.succ u) n n''.

Local Hint Constructors bin_succ bin_plus : core.

Lemma plus_S' : forall k u (n n' n'' : bin k),
  bin_plus u n n' ->
  n' -S-> n'' ->
  bin_plus (N.succ u) n n''.
Proof.
  introv H. induction H; eauto.
Qed.

Lemma bin_plus_b0 : forall k u (n n' : bin k),
  bin_plus u n n' ->
  bin_plus (N.double u) (b0 n) (b0 n').
Proof.
  introv H. induction H.
  - auto.
  - replace (N.double (N.succ u)) with (N.succ (N.succ (N.double u))) by lia.
    eauto.
Qed.

Fixpoint bin_min k : bin k :=
  match k with
  | O => bb
  | S k => b0 (bin_min k)
  end.

Fixpoint bin_max k : bin k :=
  match k with
  | O => bb
  | S k => b1 (bin_max k)
  end.

Lemma inc_to_max : forall k,
  bin_plus (pow2 k - 1) (bin_min k) (bin_max k).
Proof.
  induction k.
  - auto.
  - replace (pow2 (S k) - 1)%N with (N.succ (N.double (pow2 k - 1))).
    + eapply plus_S'.
      * apply bin_plus_b0. eassumption.
      * constructor.
    + assert (pow2 k > 0)%N by apply pow2_gt0.
      rewrite pow2_S. lia.
Qed.
