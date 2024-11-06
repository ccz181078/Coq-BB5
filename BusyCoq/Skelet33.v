(** * Skelet #33 *)

From BusyCoq Require Import Individual52 FixedBin ShiftOverflow.
From Coq Require Import PeanoNat.
From Coq Require Import List. Import ListNotations.
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
  | E, 0 => Some (1, L, A)  | E, 1 => Some (1, R, E)
  end.

From BusyCoq Require Import ShiftOverflowBins.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation P := Pos.succ.

Definition D n m : Q * tape :=
  L n <{{C}} [1; 0; 1; 0; 1; 0] *> R m.

Lemma L_inc : forall n r,
  L n <{{C}} r -->* L (N.succ n) {{B}}> r.
Proof.
  destruct n as [|n].
  - triv.
  - induction n; triv.
Qed.

Lemma R_inc_has0 : forall n l,
  has0 n ->
  l << 1 {{E}}> R n -->* l <{{A}} 0 >> R (P n).
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
  l << 1 {{E}}> R n -->* l <{{C}} R (P n).
Proof.
  introv H. generalize dependent l. induction H; triv.
Qed.

Definition E n m : Q * tape :=
  K' n <{{C}} [1; 0; 1; 0] *> R m.

Theorem start_reset : forall n m,
  all1 m ->
  D n m -->* E (N.succ_pos n) (P m)~1.
Proof.
  introv H. unfold D.
  follow L_inc. rewrite <- N.succ_pos_spec, L_as_K.
  execute. follow R_inc_all1.
  execute.
Qed.

Lemma eat_LI : forall l t,
  l <* <[1; 0; 0; 0] <{{C}} R t -->*
  l <{{C}} R (t~1~1).
Proof. triv. Qed.

Lemma eat_KI : forall l t,
  has0 t ->
  has0 (P t) ->
  l <* <[0; 1; 0; 0] <{{C}} R t -->*
  l <{{C}} R (P (P t))~0~0.
Proof.
  introv H HP. execute.
  destruct t.
  - follow R_inc_has0. execute.
  - follow R_inc_has0. execute.
    follow R_inc_has0. { inversion HP. exact H1. }
    execute.
  - inversion H.
Qed.

Fixpoint Lk {k} (n : bin k) :=
  match n with
  | bb => <[]
  | b0 n => Lk n <+ <[0; 0; 0; 0]
  | b1 n => Lk n <+ <[1; 0; 0; 0]
  end.

Lemma Lk_inc : forall k (n n' : bin k),
  n -S-> n' -> forall l r,
  l <* Lk n <{{C}} r -->* l <* Lk n' {{B}}> r.
Proof.
  introv H. induction H; triv.
Qed.

Lemma LaR_inc : forall l k (n n' : bin k) m,
  has0 m ->
  has0 (P m) ->
  n -S-> n' ->
  l <* Lk n  <{{C}} [1; 0; 1; 0] *> R m -->*
  l <* Lk n' <{{C}} [1; 0; 1; 0] *> R (P (P m)).
Proof.
  introv Hm HPm Hn. follow Lk_inc. execute.
  follow R_inc_has0. execute. follow R_inc_has0. execute.
Qed.

Lemma LaR_incs : forall l k u (n n' : bin k) m,
  bin_plus u n n' ->
  (2 * u <= b m)%N ->
  l <* Lk n  <{{C}} [1; 0; 1; 0] *> R m -->*
  l <* Lk n' <{{C}} [1; 0; 1; 0] *> R (2 * u :+ m).
Proof.
  introv H.
  generalize dependent m. induction H; introv Hr.
  - finish.
  - follow LaR_inc. { apply bgt0_has0. rewrite b_succ; lia. }
    follow IHbin_plus. { rewrite b_succ; rewrite b_succ; lia. }
    finish.
Qed.

Corollary LaR_max : forall l k m,
  (2 * (pow2 k - 1) <= b m)%N ->
  l <* Lk (bin_min k) <{{C}} [1; 0; 1; 0] *> R m -->*
  l <* Lk (bin_max k) <{{C}} [1; 0; 1; 0] *> R (2 * (pow2 k - 1) :+ m).
Proof.
  introv H.
  apply LaR_incs.
  + apply inc_to_max.
  + assumption.
Qed.

Lemma eat_bin_max : forall k l t,
  has0 t ->
  has0 (P t) ->
  l <* <[0; 1; 0; 0] <* Lk (bin_max k) <{{C}} R t -->*
  l <{{C}} [1; 0; 1; 0] *> R (P (pow4 k (P t))).
Proof.
  induction k; introv H HP.
  - follow eat_KI. finish.
  - simpl. follow eat_LI. follow (IHk l (t~1~1)%positive).
    * apply has0_0.
    * finish.
Qed.

Definition f (m : positive) (k : nat) : positive :=
  (2 * (pow2 k - 1) :+ m)~0.

Lemma has0_f : forall m k, has0 (f m k).
Proof. introv. simpl. constructor. Qed.

Local Hint Resolve has0_f : core.

Lemma drop_KI : forall l m k,
  (2 * (pow2 k - 1) <= b m)%N ->
  l <* <[0; 1; 0; 0] <* Lk (bin_min k) <{{C}} [1; 0; 1; 0] *> R m -->*
  l <{{C}} [1; 0; 1; 0] *> R (P (pow4 k (f m k)~1)).
Proof.
  introv H.
  follow LaR_max.
  replace ([1; 0; 1; 0] *> R (2 * (pow2 k - 1) :+ m)) with (R (f m k)~0)
    by reflexivity.
  follow eat_bin_max. { simpl. auto. }
  finish.
Qed.

Lemma prepare_K : forall (n : positive),
  exists (k : nat) (n' : N),
  K' n = K n' <* <[0; 1; 0; 0] <* Lk (bin_min k)
  /\ n = pow2 (S k) * n' :+ pow2' k.
Proof.
  induction n.
  - exists 0%nat, (N.pos n). auto.
  - destruct IHn as [k [n' [EIH IH]]].
    exists (S k), n'. split.
    + simpl. simpl in EIH. rewrite EIH. reflexivity.
    + lia.
  - exists 0%nat, 0%N. repeat split.
    simpl. rewrite const_unfold at 1. reflexivity.
Qed.

(* n = 1, or n starts with 11 in binary *)
Inductive leads' : positive -> Prop :=
  | leads_1 : leads' 1
  | leads_xI n : leads' n -> leads' n~1
  | leads_xO n : leads' n -> (n <> 1)%positive -> leads' n~0.

Definition leads (n : N) : Prop :=
  match n with
  | 0%N => False
  | N.pos n => leads' n
  end.

Local Hint Constructors leads' : core.

Lemma leads_add0_rev : forall n,
  leads' n~0 ->
  leads' n.
Proof.
  introv H. inverts H. assumption.
Qed.

Local Hint Resolve leads_add0_rev : core.

Lemma leads_pow2_rev : forall n k,
  leads' (pow2' k * n) ->
  leads' n.
Proof.
  induction k; auto.
Qed.

Lemma leads_pow2 : forall n,
  leads' (pow2' n) -> n = 0%nat.
Proof.
  induction n.
  - auto.
  - introv H. inverts H as H1 H2.
    apply IHn in H1. subst n. lia.
Qed.

Lemma leads_3_pow2 : forall q,
  leads' (3 * pow2' q).
Proof.
  induction q.
  * simpl. auto.
  * change (3 * pow2' (S q))%positive
      with ((3 * pow2' q)~0)%positive.
    constructor; [assumption | lia].
Qed.

Lemma leads_3_pow2_r : forall q r,
  (r < pow2' q)%positive ->
  leads' (3 * pow2' q + r).
Proof.
  induction q; introv H.
  - lia.
  - replace (3 * pow2' (S q))%positive
      with ((3 * pow2' q)~0)%positive by lia.
    destruct r as [r | r |]; cbn [Pos.add]; constructor; try lia.
    + apply IHq. lia.
    + apply IHq. lia.
    + apply leads_3_pow2.
Qed.

Lemma step_reset_odd : forall n m,
  E n~1 m -->* E n m~1~0.
Proof. introv. destruct n; execute. Qed.

Definition reset_invariant (n m : positive) :=
  leads' n /\
  (exists q r, b m = N.pos (3 * pow2' q + r) /\ 2 * n <= r < pow2' q)%positive.

Corollary reset_invariant_leads_b_m : forall n m,
  reset_invariant n m ->
  leads (b m).
Proof.
  introv [_ [q [r [H1 [H2 H3]]]]].
  rewrite H1. unfold leads.
  apply leads_3_pow2_r. assumption.
Qed.

Local Hint Resolve reset_invariant_leads_b_m : core.

Theorem step_reset : forall n m,
  (n <> 1)%positive ->
  reset_invariant n m ->
  exists n' m',
  E n m -->* E n' m' /\
  (n' < n)%positive /\
  reset_invariant n' m'.
Proof.
  introv Hgt1 [Hinv2 [q [r [Hinv1a [Hinv1b Hinv1c]]]]].
  destruct (prepare_K n) as [k [n' [EK En']]].
  destruct n' as [| n'].
  { simpl in En'. subst n. apply leads_pow2 in Hinv2. subst k. lia. }
  replace (pow2 (S k) * N.pos n' :+ pow2' k)
    with (pow2' (S k) * n' + pow2' k)%positive
    in En' by lia.
  exists n', (P (pow4 k (f m k)~1)). repeat split.
  - unfold E. rewrite EK.
    follow drop_KI. { lia. }
    finish.
  - nia.
  - rewrite En' in Hinv2.
    replace (pow2' (S k) * n' + pow2' k)%positive
      with (pow2' k * n'~1)%positive in Hinv2 by lia.
    apply leads_pow2_rev in Hinv2.
    inverts Hinv2. assumption.
  - exists (q + 2 * k + 2).
    exists (pow2' (2 * k + 2) * (r - 2 * pow2' k + 2)
              + 3 * pow2' (2 * k) - 2)%positive.
    repeat split.
    + destruct k. { simpl b. rewrite Hinv1a. lia. }
      simpl pow4. rewrite pow4_shift. simpl b. rewrite b_pow4.
      replace (b (f m (S k))~1)
        with (4 * b (2 * (pow2 (S k) - 1) :+ m) + 2)%N by (simpl b; lia).
      rewrite b_add by lia. rewrite Hinv1a.
      replace (2 * S k) with (S (S (2 * k))) by lia. nia.
    + nia.
    + nia.
Qed.

Corollary do_reset : forall n m,
  reset_invariant n m ->
  exists m',
  E n m -->* E 1 m' /\
  leads (b m').
Proof.
  induction n as [n IH] using positive_strong_induction.
  introv Hinv.
  destruct (Pos.eq_dec n 1) as [En | Hgt1].
  { (* n = 1 *) subst n. exists m. eauto. }
  destruct (step_reset n m Hgt1 Hinv)
    as [n' [m' [Hsteps [Hless Hinv']]]].
  destruct (IH n' Hless m' Hinv') as [m'' [Hsteps' Hleads']].
  exists m''. eauto using evstep_trans.
Qed.

Lemma E_start : forall m,
  E 1 m -->+ D 0 m~1.
Proof. execute. Qed.

Theorem E_next : forall m,
  leads (b m) ->
  exists m',
  E 1 m -->+ E 1 m' /\
  leads (b m').
Proof.
  introv Hinvariant.
  destruct (b m) as [| bm] eqn:Ebm. { destruct Hinvariant. }
  unfold leads in Hinvariant.
  assert (Hfinish: exists m', E bm (P (bm + m))~0~1~1~0 -->* E 1 m' /\
    leads (b m')).
  { apply do_reset. split.
    - assumption.
    - replace (bm + m)%positive with (b m :+ m) by lia.
      destruct (b_add_pow2 m) as [k Ek]. rewrite Ek.
      replace (b (pow2' k)~0~1~1~0) with (16 * (b (pow2' k)) + 9)%N
        by (simpl b; lia).
      rewrite b_pow2.
      exists (S (S k)), (pow2' (S (S k)) - 7)%positive.
      lia. }
  destruct Hfinish as [m' [Hfinish Hleads']].
  exists m'. split.
  - eapply progress_evstep_trans. { apply E_start. }
    follow D_finish. rewrite N.add_0_r.
    follow start_reset. simpl b. rewrite Ebm.
    replace (N.succ_pos (N.double (N.pos bm)))
      with (bm~1)%positive by lia.
    replace (P (N.double (N.pos bm) :+ m~1))
      with ((P (bm + m))~0)%positive by lia.
    (* This is only necessary as otherwise the reset invariant is tight enough
       that the fact that subtraction on [N] and [positive] is saturating
       shows up, which makes actually proving it a bit hairy. *)
    follow step_reset_odd.
    apply Hfinish.
  - apply Hleads'.
Qed.

Theorem nonhalt : ~ halts tm c0.
Proof.
  apply multistep_nonhalt with (E 1 17). { execute. }
  apply progress_nonhalt_cond with (C := E 1) (P := fun m => leads (b m)).
  - intros m Hleads.
    destruct (E_next m Hleads) as [m' [Hsteps Hleads']].
    eauto.
  - repeat constructor. discriminate.
Qed.
