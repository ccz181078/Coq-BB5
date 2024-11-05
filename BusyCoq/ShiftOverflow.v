(** * Things common to shift-overflow machines *)

(** This is mostly the [b] function, which expresses the distance to the
    next power of two. *)

From BusyCoq Require Import Helper.
From Coq Require Import Lia.
From Coq Require Import PArith.BinPos PArith.Pnat.
From Coq Require Import NArith.BinNat NArith.Nnat.
Set Default Goal Selector "!".

(** We use a definition of [b] shifted by 1 compared to the informal proof, i.e.
    we can do [n + b n] is the farthest we can go without reaching a new power
    of two. *)
Fixpoint b (n : positive) : N :=
  match n with
  | xH => N0
  | xO n' => N.succ_double (b n')
  | xI n' => N.double (b n')
  end.

Inductive has0 : positive -> Prop :=
  | has0_0 n: has0 (n~0)
  | has0_1 n: has0 n -> has0 (n~1).

#[export] Hint Constructors has0 : core.

Inductive all1 : positive -> Prop :=
  | all1_H:   all1 1
  | all1_1 n: all1 n -> all1 (n~1).

Lemma b0_all1 : forall n, b n = N0 -> all1 n.
Proof.
  induction n; introv H; simpl in H.
  - apply all1_1, IHn. lia.
  - lia.
  - apply all1_H.
Qed.

#[export] Hint Resolve b0_all1 : core.

Lemma bgt0_has0 : forall n, (b n > 0)%N -> has0 n.
Proof.
  induction n; introv H; simpl in *.
  - apply has0_1, IHn. lia.
  - apply has0_0.
  - inverts H.
Qed.

#[export] Hint Extern 1 (has0 _) => apply bgt0_has0; lia : core.

Lemma b_succ : forall n, (b n > 0)%N -> b (Pos.succ n) = N.pred (b n).
Proof. induction n; simpl; lia. Qed.

Lemma b_add : forall u n,
  (u <= b n -> b (u :+ n) = b n - u)%N.
Proof.
  (* XXX: this is very ugly, why does [induction u using N.induction] not work here? *)
  apply (N.induction (fun u => forall n, u <= b n -> b (u :+ n) = b n - u)%N).
  - auto with *.
  - introv H. simpl. lia.
  - intros u IH n H.
    rewrite het_add_succ_l, b_succ; rewrite IH; lia.
Qed.

Corollary b_add_self : forall n,
  b (b n :+ n) = 0%N.
Proof.
  introv. rewrite b_add; lia.
Qed.

#[export] Hint Immediate b_add_self : core.

Lemma b0_succ : forall n, b n = 0%N -> b (Pos.succ n) = (Npos n).
Proof.
  introv H. apply b0_all1 in H.
  induction H.
  - reflexivity.
  - simpl. rewrite IHall1. lia.
Qed.

Lemma all1_succ_pow2 : forall n,
  all1 n ->
  exists k, Pos.succ n = pow2' k.
Proof.
  introv H. induction H.
  - exists 1. reflexivity.
  - destruct IHall1 as [k IH].
    exists (S k). lia.
Qed.

Corollary b_add_pow2 : forall n,
  exists k, Pos.succ (b n :+ n) = pow2' k.
Proof.
  introv. apply all1_succ_pow2. auto.
Qed.

Lemma b_pow2 : forall k,
  (b (pow2' k) = pow2 k - 1)%N.
Proof.
  induction k; simpl; lia.
Qed.

Fixpoint pow4 (k : nat) (n : positive) : positive :=
  match k with
  | O => n
  | S k => pow4 k (n~0~0)
  end.

Lemma pow4_shift : forall k n,
  (pow4 k n~0~0 = (pow4 k n)~0~0)%positive.
Proof.
  induction k; introv.
  - reflexivity.
  - simpl. rewrite IHk. reflexivity.
Qed.

Lemma b_pow4 : forall k n,
  (b (pow4 k n) = pow2 (2 * k) * (b n + 1) - 1)%N.
Proof.
  unfold pow2.
  induction k; introv; simpl pow4; simpl pow2'.
  - lia.
  - rewrite pow4_shift. simpl b.
    rewrite IHk.
    rewrite <- plus_n_Sm.
    lia.
Qed.
