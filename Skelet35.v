(** * Skelet #35 *)

(** Note: this is mostly a copy of Skelet34.v – the machines are similar
    enough that the proofs check out. *)

From BusyCoq Require Import Individual52 FixedBin ShiftOverflow.
From Coq Require Import PeanoNat.
From Coq Require Import Lia.
From Coq Require Import PArith.BinPos PArith.Pnat.
From Coq Require Import NArith.BinNat NArith.Nnat.
Set Default Goal Selector "!".

Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => Some (1, L, C)
  | B, 0 => Some (0, R, C)  | B, 1 => Some (0, R, B)
  | C, 0 => Some (1, L, D)  | C, 1 => Some (0, L, A)
  | D, 0 => Some (1, L, E)  | D, 1 => None
  | E, 0 => Some (1, L, A)  | E, 1 => Some (0, L, A)
  end.

From BusyCoq Require Import ShiftOverflowBins.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation P := Pos.succ.

Definition D n m : Q * tape :=
  L n <{{C}} [1; 0; 1; 0] *> R m.

Lemma L_inc : forall n r,
  L n <{{C}} r -->* L (N.succ n) {{B}}> r.
Proof.
  destruct n as [|n].
  - triv.
  - induction n; triv.
Qed.

Lemma R_inc_has0 : forall n l,
  has0 n ->
  l << 0 {{C}}> R n -->* l <{{A}} 0 >> R (P n).
Proof.
  introv H. generalize dependent l. induction H; introv.
  - triv.
  - execute. follow. execute.
Qed.

Corollary D_inc : forall n m,
  has0 m ->
  D n m -->* D (N.succ n) (P m).
Proof.
  introv H. unfold D.
  follow L_inc. execute.
  follow R_inc_has0. execute.
Qed.

Corollary D_run : forall u n m,
  (u <= b m)%N ->
  D n m -->* D (u + n) (u :+ m).
Proof.
  induction u using N.peano_ind; introv H.
  - finish.
  - follow D_inc.
    follow IHu. { rewrite b_succ; lia. }
    finish.
Qed.

Corollary D_finish : forall n m,
  D n m -->* D (b m + n) (b m :+ m).
Proof. introv. apply D_run. lia. Qed.

Lemma R_inc_all1 : forall n l,
  all1 n ->
  l << 0 {{C}}> R n -->* l <{{C}} R (P n).
Proof.
  introv H. generalize dependent l. induction H; triv.
Qed.

Definition E n a m : Q * tape :=
  K n <{{C}} [1; 0; 1; a] *> R m.

Theorem start_reset : forall n m,
  all1 m ->
  D n m -->* E (N.succ n) 1 (P m).
Proof.
  introv H. unfold D.
  follow L_inc. rewrite L_as_K.
  execute. follow R_inc_all1.
  execute.
Qed.

Corollary start_reset' : forall n m,
  all1 m ->
  D n m -->+ E (N.succ n) 1 (P m).
Proof.
  introv H.
  apply evstep_progress.
  - apply start_reset. assumption.
  - discriminate.
Qed.

Lemma eat_LI : forall l t,
  l <* <[1; 0; 0; 0] <{{C}} R t -->*
  l <{{C}} R (t~1~1).
Proof. triv. Qed.

Lemma eat_KI : forall l t,
  has0 t ->
  l <* <[0; 1; 0; 0] <{{C}} R t -->*
  l <{{C}} R (4 * P t).
Proof.
  introv H. execute.
  follow R_inc_has0. execute.
Qed.

Lemma Lk_inc : forall k (n n' : bin k),
  n -S-> n' -> forall l r,
  l <* Lk n <{{C}} r -->* l <* Lk n' {{B}}> r.
Proof.
  introv H. induction H; triv.
Qed.

Lemma LaR_inc : forall l k (n n' : bin k) a m,
  has0 m ->
  n -S-> n' ->
  l <* Lk n  <{{C}} [1; 0; 1; a] *> R m -->*
  l <* Lk n' <{{C}} [1; 0; 1; a] *> R (P m).
Proof.
  introv Hm Hn. destruct a;
    follow Lk_inc; execute; follow R_inc_has0; execute.
Qed.

Lemma LaR_incs : forall l k u (n n' : bin k) a m,
  bin_plus u n n' ->
  (u <= b m)%N ->
  l <* Lk n  <{{C}} [1; 0; 1; a] *> R m -->*
  l <* Lk n' <{{C}} [1; 0; 1; a] *> R (u :+ m).
Proof.
  introv H.
  generalize dependent m. induction H; introv Hr.
  - finish.
  - follow LaR_inc.
    follow IHbin_plus. { rewrite b_succ; lia. }
    finish.
Qed.

Corollary LaR_max : forall l k a m,
  (pow2 k - 1 <= b m)%N ->
  l <* Lk (bin_min k) <{{C}} [1; 0; 1; a] *> R m -->*
  l <* Lk (bin_max k) <{{C}} [1; 0; 1; a] *> R (pow2 k - 1 :+ m).
Proof.
  introv H.
  apply LaR_incs.
  + apply inc_to_max.
  + assumption.
Qed.

Lemma eat_bin_max : forall k l t,
  has0 t ->
  l <* <[0; 1; 0; 0] <* Lk (bin_max k) <{{C}} R t -->*
  l <{{C}} [1; 0; 1; 0] *> R (pow4 k (P t)).
Proof.
  induction k; introv H.
  - follow eat_KI. finish.
  - simpl. follow eat_LI. follow (IHk l (t~1~1)%positive). finish.
Qed.

Definition f (m : positive) (a : sym) (k : nat) : positive :=
  let t := (pow2 k - 1 :+ m) in
  match a with
  | 0 => t~0~0
  | 1 => t~1~0
  end.

Lemma has0_f : forall m a k, has0 (f m a k).
Proof. destruct a; introv; simpl; constructor. Qed.

Local Hint Resolve has0_f : core.

Lemma f_lt : forall m a k, exists x,
  (P (f m a k) = 4 * (pow2 k - 1 :+ m) + x /\
  x <= 3)%positive.
Proof.
  introv. destruct a.
  - exists 1%positive. unfold f. lia.
  - exists 3%positive. unfold f. lia.
Qed.

Lemma drop_KI : forall l m k a,
  (pow2 k - 1 <= b m)%N ->
  l <* <[0; 1; 0; 0] <* Lk (bin_min k)  <{{C}} [1; 0; 1; a] *> R m -->*
  l <{{C}} [1; 0; 1; 0] *> R (pow4 k (P (f m a k))).
Proof.
  introv H.
  follow LaR_max.
  replace ([1; 0; 1; a] *> R (pow2 k - 1 :+ m)) with (R (f m a k))
    by (destruct a; reflexivity).
  follow eat_bin_max. finish.
Qed.

Lemma prepare_K : forall (n : N), (n > 0)%N -> exists (k : nat) (n' : N),
  K n = K n' <* <[0; 1; 0; 0] <* Lk (bin_min k)
  /\ (n = pow2 k + pow2 (S k) * n')%N.
Proof.
  destruct n as [| n]. { lia. }
  intros _.
  induction n.
  - exists O, (Npos n). auto.
  - destruct IHn as [k [n' [EIH IH]]].
    exists (S k), n'. split.
    + simpl. simpl in EIH. rewrite EIH. reflexivity.
    + lia.
  - exists O, N0. repeat split.
    simpl. rewrite const_unfold at 1. reflexivity.
Qed.

Theorem step_reset : forall n m a,
  (n <= b m)%N ->
  (n > 0)%N ->
  exists (n' : N) (m' : positive),
  E n a m -->* E n' 0 m' /\
  (n' < n)%N /\ (n' <= b m')%N.
Proof.
  introv Hinvariant Hgt0.
  destruct (prepare_K n Hgt0) as [k [n' [EK En']]].
  exists n'. eexists. repeat split.
  - unfold E. rewrite EK.
    follow drop_KI. { lia. }
    finish.
  - rewrite En'. nia.
  - destruct (f_lt m a k) as [x [E Hx]].
    rewrite b_pow4, E.
    replace (4 * (pow2 k - 1 :+ m) + x)%positive
      with (N.pos x :+ 4 * (pow2 k - 1 :+ m))
      by lia.
    rewrite b_add by (simpl; lia).
    replace (b (4 * (pow2 k - 1 :+ m)))
      with (N.succ_double (N.succ_double (b (pow2 k - 1 :+ m))))
      by reflexivity.
    transitivity (b (pow2 k - 1 :+ m)).
    + rewrite b_add by lia. nia.
    + nia.
Qed.

Corollary do_reset : forall n m a,
  (n <= b m)%N ->
  (n > 0)%N ->
  exists m',
  E n a m -->* E 0 0 m'.
Proof.
  induction n using N_strong_induction; introv Hinvariant Hgt0.
  destruct (step_reset n m a Hinvariant Hgt0)
    as [n' [m' [Hsteps [Hless Hinvariant']]]].
  destruct n' as [| n'].
  - exists m'. exact Hsteps.
  - assert (G: exists m'', E (Npos n') 0 m' -->* E 0 0 m'').
    { apply H; try assumption; reflexivity. }
    destruct G as [m'' G]. exists m''.
    follow Hsteps. apply G.
Qed.

Theorem D_next : forall m, exists m',
  D 0 m -->+ D 0 m'.
Proof.
  introv.
  assert (H: exists m', E (N.succ (b m)) 1 (P (b m :+ m)) -->* E 0 0 m').
  { apply do_reset; try lia.
    rewrite b0_succ.
    - lia.
    - apply b_add_self. }
  destruct H as [m' H]. exists m'.
  eapply evstep_progress_trans. { apply D_finish. }
  eapply progress_evstep_trans. { apply start_reset'. auto. }
  rewrite N.add_0_r.
  follow H. finish.
Qed.

Theorem nonhalt : ~ halts tm c0.
Proof.
  apply multistep_nonhalt with (D 0 1441). { execute. }
  apply progress_nonhalt_simple with (C := D 0). intro m.
  destruct (D_next m) as [m' Hrun]. eauto.
Qed.
