(** * Skelet #26 *)

From BusyCoq Require Import Individual52 FixedBin ShiftOverflow.
From Coq Require Import PeanoNat.
From Coq Require Import List. Import ListNotations.
From Coq Require Import Lia.
From Coq Require Import PArith.BinPos PArith.Pnat.
From Coq Require Import NArith.BinNat NArith.Nnat.
Set Default Goal Selector "!".

Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => Some (1, L, D)
  | B, 0 => Some (1, R, C)  | B, 1 => Some (0, R, B)
  | C, 0 => Some (1, L, A)  | C, 1 => Some (1, R, C)
  | D, 0 => Some (1, L, E)  | D, 1 => Some (0, L, A)
  | E, 0 => Some (1, L, C)  | E, 1 => None
  end.

From BusyCoq Require Import ShiftOverflowBins.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation P := Pos.succ.

Definition D n a m : Q * tape :=
  L n <{{D}} 1 >> 0 >> 1 >> a >> R m.

Lemma L_inc : forall n r,
  L n <{{D}} r -->* L (N.succ n) {{B}}> r.
Proof.
  destruct n as [|n].
  - triv.
  - induction n; triv.
Qed.

Lemma R_inc_has0 : forall n l,
  has0 n ->
  l {{C}}> R n -->* l <{{D}} R (P n).
Proof.
  introv H. generalize dependent l. induction H; introv.
  - triv.
  - execute. follow. execute.
Qed.

Corollary D_inc : forall n a m,
  has0 m ->
  D n a m -->* D (N.succ n) a (P m).
Proof.
  introv H. unfold D.
  follow L_inc. cases a; execute; follow R_inc_has0; execute.
Qed.

Corollary D_run : forall u n a m,
  (u <= b m)%N ->
  D n a m -->* D (u + n) a (u :+ m).
Proof.
  induction u using N.peano_ind; introv H.
  - finish.
  - follow D_inc.
    follow IHu. { rewrite b_succ; lia. }
    finish.
Qed.

Corollary D_finish : forall n a m,
  D n a m -->* D (b m + n) a (b m :+ m).
Proof. introv. apply D_run. lia. Qed.

Lemma R_inc_all1 : forall n l,
  all1 n ->
  l << 1 {{C}}> R n -->* l <{{D}} R (P n).
Proof.
  introv H. generalize dependent l. induction H; triv.
Qed.

Fixpoint J' (n : positive) : side :=
  match n with
  | xH =>    const 0 << 1
  | xO n => J' n << 0 << 0 << 0 << 0
  | xI n => J' n << 0 << 0 << 0 << 1
  end.

Definition J (n : N) : side :=
  match n with
  | N0 => const 0
  | Npos n => J' n
  end.

Lemma L_as_J : forall n,
  L n = J n << 0 << 0 << 0.
Proof.
  destruct n as [| n].
  - repeat rewrite <- const_unfold. reflexivity.
  - simpl. induction n; simpl; try rewrite IHn; reflexivity.
Qed.

Lemma K_as_J : forall n,
  K n = J n << 0 << 0.
Proof.
  destruct n as [| n].
  - repeat rewrite <- const_unfold. reflexivity.
  - simpl. induction n; simpl; try rewrite IHn; reflexivity.
Qed.

Definition E0 n a m : Q * tape :=
  K n <{{D}} 1 >> 0 >> 1 >> a >> R m.

Definition E1 n a m : Q * tape :=
  J n <{{D}} 1 >> 0 >> 1 >> a >> R m.

Theorem start_reset0 : forall n m,
  all1 m ->
  D n 0 m -->+ E0 (N.succ n) 1 (P m).
Proof.
  introv H. unfold D.
  follow L_inc. rewrite L_as_K.
  execute. follow R_inc_all1.
  execute.
Qed.

(* For k>=1, D(n, 1, 2^k-1) -->+ E1(2(n+1), 0, 2^{k-1}) *)
Theorem start_reset1 : forall n m,
  all1 m ->
  exists m',
  (m'~0 = P m)%positive /\
  D n 1 m -->+ E1 (N.double (N.succ n)) 0 m'.
Proof.
  introv H. unfold D. induction H.
  - exists 1%positive. split. { reflexivity. }
    follow L_inc. rewrite L_as_J. cases n; execute.
  - destruct IHall1 as [m'' [H1 _]].
    exists (m''~0)%positive. split. { lia. }
    follow L_inc.
    start_progress.
    rewrite L_as_J. follow R_inc_all1.
    rewrite H1. cases n; execute.
Qed.

Lemma eat_LI : forall l t,
  l << 1 << 0 << 0 << 0 <{{D}} R t -->*
  l <{{D}} R (t~1~1).
Proof. triv. Qed.

Lemma eat_KI : forall l t,
  has0 t ->
  l << 0 << 1 << 0 << 0 <{{D}} R t -->*
  l <{{D}} R (P t)~1~0.
Proof.
  introv H. execute.
  follow R_inc_has0. execute.
Qed.

Lemma eat_JI : forall l t,
  has0 t ->
  l << 0 << 1 <{{D}} R t -->*
  l <{{D}} R (P t)~0.
Proof.
  introv H. execute.
  follow R_inc_has0. execute.
Qed.

Fixpoint Lk {k} (n : bin k) (l : side) :=
  match n with
  | bb => l
  | b0 n => Lk n l << 0 << 0 << 0 << 0
  | b1 n => Lk n l << 1 << 0 << 0 << 0
  end.

Lemma Lk_inc : forall k (n n' : bin k),
  n -S-> n' -> forall l r,
  Lk n l <{{D}} r -->* Lk n' l {{B}}> r.
Proof.
  introv H. induction H; triv.
Qed.

Lemma LaR_inc : forall l k (n n' : bin k) a m,
  has0 m ->
  n -S-> n' ->
  Lk n  l <{{D}} 1 >> 0 >> 1 >> a >> R m -->*
  Lk n' l <{{D}} 1 >> 0 >> 1 >> a >> R (P m).
Proof.
  introv Hm Hn. destruct a;
    follow Lk_inc; execute; follow R_inc_has0; execute.
Qed.

Lemma LaR_incs : forall l k u (n n' : bin k) a m,
  bin_plus u n n' ->
  (u <= b m)%N ->
  Lk n  l <{{D}} 1 >> 0 >> 1 >> a >> R m -->*
  Lk n' l <{{D}} 1 >> 0 >> 1 >> a >> R (u :+ m).
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
  Lk (bin_min k) l <{{D}} 1 >> 0 >> 1 >> a >> R m -->*
  Lk (bin_max k) l <{{D}} 1 >> 0 >> 1 >> a >> R (pow2 k - 1 :+ m).
Proof.
  introv H.
  apply LaR_incs.
  + apply inc_to_max.
  + assumption.
Qed.

Lemma eat_bin_max0 : forall k l t,
  has0 t ->
  Lk (bin_max k) (l << 0 << 1 << 0 << 0) <{{D}} R t -->*
  l <{{D}} 1 >> 0 >> 1 >> 1 >> R (pow4 k (P t)).
Proof.
  induction k; introv H.
  - follow eat_KI. finish.
  - simpl. follow eat_LI. follow (IHk l (t~1~1)%positive). finish.
Qed.

Lemma eat_bin_max1 : forall k l t,
  has0 t ->
  Lk (bin_max k) (l << 0 << 1) <{{D}} R t -->*
  l <{{D}} 1 >> 0 >> R (pow4 k (P t)).
Proof.
  induction k; introv H.
  - follow eat_JI. finish.
  - simpl. follow eat_LI. follow (IHk l (t~1~1)%positive). finish.
Qed.

Definition f (m : positive) (a : sym) (k : nat) : positive :=
  let t := (pow2 k - 1 :+ m) in
  match a with
  | 0 => t~0~0
  | 1 => t~1~0
  end.

Definition f1 (m : positive) (a : sym) (k : nat) : positive :=
  let t := (pow2 k - 1 :+ m) in
  match a with
  | 0 => t~0
  | 1 => t~1
  end.

Lemma f_as_f1 : forall m a k, ((f m a k) = (f1 m a k)~0)%positive.
Proof. destruct a; introv; simpl; constructor. Qed.

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
  Lk (bin_min k) (l << 0 << 1 << 0 << 0) <{{D}} 1 >> 0 >> 1 >> a >> R m -->*
  l <{{D}} 1 >> 0 >> 1 >> 1 >> R (pow4 k (P (f m a k))).
Proof.
  introv H.
  follow LaR_max.
  replace (1 >> 0 >> 1 >> a >> R (pow2 k - 1 :+ m)) with (R (f m a k))
    by (destruct a; reflexivity).
  follow eat_bin_max0. finish.
Qed.

Lemma drop_JI : forall l m k a,
  (pow2 k - 1 <= b m)%N ->
  Lk (bin_min k) (l << 0 << 1) <{{D}} 1 >> 0 >> 1 >> a >> R m -->*
  l <{{D}} 1 >> 0 >> R (pow4 k (P (f m a k))).
Proof.
  introv H.
  follow LaR_max.
  replace (1 >> 0 >> 1 >> a >> R (pow2 k - 1 :+ m)) with (R (f m a k))
    by (destruct a; reflexivity).
  follow eat_bin_max1. finish.
Qed.

Lemma prepare_K : forall (n : N), (n > 0)%N -> exists (k : nat) (n' : N),
  K n = Lk (bin_min k) (K n' << 0 << 1 << 0 << 0)
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

Lemma prepare_J : forall (n : N) (k : nat) (n' : N),
  (n = pow2 k + pow2 (S k) * n')%N ->
  J n = Lk (bin_min k) (J n' << 0 << 0 << 0 << 1).
Proof.
  introv. revert n. induction k; introv H.
  - rewrite H. cases n'; try reflexivity.
    repeat rewrite <- const_unfold. reflexivity.
  - replace (J n) with (J (pow2 k + pow2 (S k) * n') << 0 << 0 << 0 << 0).
    { rewrite IHk; reflexivity. }
    replace n with (2 * (pow2 k + pow2 (S k) * n'))%N by lia.
    generalize (pow2 k + pow2 (S k) * n')%N. intro n''.
    cases n''; try reflexivity. repeat rewrite <- const_unfold. reflexivity.
Qed.

Definition reset_invariant (m : positive) :=
  (m >= 2)%positive /\
  exists k n', N.succ (b m) = (pow2 k + pow2 (S k) * n')%N /\ (n' >= 2)%N.

Theorem step_reset0 : forall n m a,
  (n <= b m)%N ->
  (n > 0)%N ->
  exists (n' : N) (m' : positive),
  E0 n a m -->* E0 n' 1 m' /\
  (n' < n)%N /\ (n' <= b m')%N /\ reset_invariant m'.
Proof.
  introv Hinvariant Hgt0.
  destruct (prepare_K n Hgt0) as [k [n' [EK En']]].
  exists n'. eexists. repeat split.
  - unfold E0. rewrite EK.
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
  - cases k; simpl pow4; try rewrite pow4_shift; lia.
  - exists (2 * k) (b (f1 m a k)).
    split. { rewrite b_pow4, f_as_f1. simpl b. lia. }
    assert (H: (b (pow2 k - 1 :+ m) >= 1)%N). { rewrite b_add; lia. }
    cases a; simpl b; simpl b in H; lia.
Qed.

Corollary do_reset0 : forall n m a,
  (n <= b m)%N ->
  (n > 0)%N ->
  exists m',
  E0 n a m -->* E0 0 1 m' /\
  reset_invariant m'.
Proof.
  induction n using N_strong_induction; introv Hinvariant Hgt0.
  destruct (step_reset0 n m a Hinvariant Hgt0)
    as [n' [m' [Hsteps [Hless [Hinv1' Hinv2']]]]].
  destruct n' as [| n'].
  - exists m'. split; assumption.
  - assert (G: exists m'', E0 (Npos n') 1 m' -->* E0 0 1 m'' /\
      reset_invariant m'').
    { apply H; try assumption; reflexivity. }
    destruct G as [m'' [G1 G2]]. exists m''. split; try assumption.
    follow Hsteps. apply G1.
Qed.

(* todo: find a better place for this *)
Lemma pow4_shift1 : forall k n,
  (pow4 k n~0 = (pow4 k n)~0)%positive.
Proof.
  induction k; introv.
  - reflexivity.
  - simpl. rewrite IHk. reflexivity.
Qed.

Theorem step_reset1 : forall n m a,
  (n <= 4 * b m)%N ->
  (exists (k : nat) (n' : N),
    (* do (S k) to ensure n is even *)
    (n = (pow2 (S k) + pow2 (S (S k)) * n'))%N /\
    (pow2 (S k) <= b m)%N) ->
  exists (n' : N) (m' : positive),
  E1 n a m -->* E0 n' 0 m' /\
  (n' < n)%N /\ (n' <= b m')%N /\ (reset_invariant m').
Proof.
  introv [k [n' [Hinv2a Hinv2b]]].
  exists n'. eexists. repeat split.
  - unfold E1. rewrite (prepare_J _ _ _ Hinv2a).
    follow drop_JI. { lia. }
    unfold E0. rewrite K_as_J. finish.
    simpl pow4. rewrite pow4_shift1. reflexivity.
  - rewrite Hinv2a. nia.
  - destruct (f_lt m a (S k)) as [x [E Hx]].
    rewrite b_pow4, E.
    replace (4 * (pow2 (S k) - 1 :+ m) + x)%positive
      with (N.pos x :+ 4 * (pow2 (S k) - 1 :+ m))
      by lia.
    unfold b. rewrite b_add by (simpl; lia).
    replace (b (4 * (pow2 (S k) - 1 :+ m)))
      with (N.succ_double (N.succ_double (b (pow2 (S k) - 1 :+ m))))
      by reflexivity.
    transitivity (b (pow2 (S k) - 1 :+ m)).
    + rewrite b_add by lia. nia.
    + nia.
  - rewrite pow4_shift1. lia.
  - exists (S (2 * k)) (b (f1 m a (S k))).
    split. { rewrite b_pow4, f_as_f1. simpl b. lia. }
    assert (Hb_pos: (b (pow2 (S k) - 1 :+ m) >= 1)%N). { rewrite b_add; lia. }
    cases a; simpl b; simpl b in Hb_pos; lia.
Qed.

Corollary do_reset1 : forall n m a,
  (n <= 4 * b m)%N ->
  (exists (k : nat) (n' : N),
    (* do (S k) to ensure n is even *)
    (n = (pow2 (S k) + pow2 (S (S k)) * n'))%N /\
    (pow2 (S k) <= b m)%N) ->
  exists m' a',
  E1 n a m -->* E0 0 a' m' /\ reset_invariant m'.
Proof.
  introv Hinv1 Hinv2.
  destruct (step_reset1 n m a Hinv1 Hinv2)
    as [n' [m' [Hsteps [Hless [Hinv1' [Hinv2a' Hinv2b']]]]]].
  destruct n' as [| n'].
  - exists m' 0. repeat split; assumption.
  - assert (G: exists m'', E0 (Npos n') 0 m' -->* E0 0 1 m''
      /\ reset_invariant m'').
    { apply do_reset0; lia. }
    destruct G as [m'' [G1 G2]]. exists m'' 1.
    split; try assumption. follow Hsteps. apply G1.
Qed.

Theorem D0_next : forall m, exists m',
  D 0 0 m -->+ D 0 1 m' /\ reset_invariant m'.
Proof.
  introv.
  assert (H: exists m', E0 (N.succ (b m)) 1 (P (b m :+ m)) -->* E0 0 1 m' /\
    reset_invariant m').
  { apply do_reset0; try lia.
    rewrite b0_succ.
    - lia.
    - apply b_add_self. }
  destruct H as [m' [H1 H2]]. exists m'. split; try assumption.
  eapply evstep_progress_trans. { apply D_finish. }
  eapply progress_evstep_trans. { apply start_reset0. auto. }
  rewrite N.add_0_r.
  follow H1. finish.
Qed.

Theorem D1_next : forall m,
  reset_invariant m ->
  exists m' a',
  D 0 1 m -->+ D 0 a' m' /\
  reset_invariant m'.
Proof.
  introv [Hinv1 [k [n' [Hinv2a Hinv2b]]]].
  destruct (start_reset1 (b m) (b m :+ m)) as [m' [Hm' H1]].
  { apply b0_all1. apply b_add_self. }
  assert (H: exists m'' a'', E1 (N.double (N.succ (b m))) 0 m' -->* E0 0 a'' m'' /\
    (m'' >= 2)%positive /\
    (exists k n', N.succ (b m'') = (pow2 k + pow2 (S k) * n')%N /\ (n' >= 2)%N)).
  { apply do_reset1.
    - transitivity (N.double (N.pred (b m'~0)))%N; try (simpl b; lia).
      rewrite Hm'. rewrite b0_succ; try apply b_add_self. lia.
    - exists k n'. split. { lia. }
      assert ((2 * pow2 (S k) + 2 <= 2 * b m' + 2)%N); try lia.
      transitivity (b m'~0); try (simpl b; lia).
      rewrite Hm'. rewrite b0_succ; try apply b_add_self.
      nia. }
  destruct H as [m'' [a'' [H2 [Hinv2a' Hinv2b']]]].
  exists m'' a''. repeat split; try assumption.
  eapply evstep_progress_trans. { apply D_finish. }
  rewrite N.add_0_r. eapply progress_evstep_trans. { apply H1. }
  follow H2. finish.
Qed.

Theorem D_next : forall m a,
  reset_invariant m ->
  exists m' a',
  D 0 a m -->+ D 0 a' m' /\
  reset_invariant m'.
Proof.
  introv Hinv.
  cases a.
  - destruct (D0_next m) as [m' H]. exists m' 1. assumption.
  - destruct (D1_next m Hinv) as [m' [a' H]]. exists m' a'. assumption.
Qed.

Theorem D0_nonhalt : forall m,
  ~ halts tm (D 0 0 m).
Proof.
  introv.
  destruct (D0_next m) as [m' [Hrun Hinv]].
  apply multistep_nonhalt with (D 0 1 m'). { auto using progress_evstep. }
  apply progress_nonhalt_cond with (i0 := (m', 1))
    (C := fun '(m, a) => D 0 a m)
    (P := fun '(m, a) => reset_invariant m).
  - clear m m' Hrun Hinv.
    intros [m a] Hinv.
    destruct (D_next m a Hinv) as [m' [a' [Hsteps Hinv']]].
    eexists (_, _). eauto.
  - eauto.
Qed.

Corollary nonhalt : ~ halts tm c0.
Proof.
  apply multistep_nonhalt with (D 0 0 11). { execute. }
  apply D0_nonhalt.
Qed.
