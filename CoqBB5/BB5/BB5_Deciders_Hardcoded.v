Require Import ZArith.
Require Import Lia.
Require Import List.

From CoqBB5 Require Import Prelims.
From CoqBB5 Require Import BB5_Encodings.
From CoqBB5 Require Import Tactics.
From CoqBB5 Require Import BB5_Statement.
From CoqBB5 Require Import TM.
From CoqBB5 Require Import TNF.

From CoqBB5 Require Import Deciders_Common.
From CoqBB5 Require Import Decider_Halt.
From CoqBB5 Require Import Decider_Halt_BB5.
From CoqBB5 Require Import Decider_Loop.
From CoqBB5 Require Import Decider_NGramCPS.
From CoqBB5 Require Import Decider_RepWL.
From CoqBB5 Require Import Verifier_FAR.
From CoqBB5 Require Import Verifier_WFAR.
From CoqBB5 Require Import BB5_Sporadic_Machines.

Set Warnings "-abstract-large-number".

(* Deciders called with hardcoded parameters*)
Inductive DeciderType :=
| NG(hlen len:nat)
| NG_LRU(len:nat)
| RWL(len m:nat)
| DNV(n:nat)(f:nat->Σ->nat)
| WA(max_d:BinNums.Z)(n_l:nat)(f_l:nat->Σ->(nat*BinNums.Z))(n_r:nat)(f_r:nat->Σ->(nat*BinNums.Z))
| Ha
| Lp1
| Holdout.

Fixpoint find_tm(tm:TM Σ)(ls:list (TM Σ)):bool :=
match ls with
| nil => false
| h::t => tm_eqb tm h ||| find_tm tm t
end.

Definition holdout_checker tm := if find_tm tm tm_holdouts_13 then Result_NonHalt else Result_Unknown.

Definition getDecider(x:DeciderType) :=
match x with
| NG hlen len =>
  match hlen with
  | O => NGramCPS_decider_impl2 len len 5000001
  | _ => NGramCPS_decider_impl1 hlen len len 5000001
  end
| NG_LRU len =>
  NGramCPS_LRU_decider len len 5000001
| RWL len mnc => RepWL_ES_decider len mnc 320 150001
| DNV n f => dfa_nfa_verifier n f
| WA max_d n_l f_l n_r f_r => MITM_WDFA_verifier max_d n_l f_l n_r f_r 10000000
| Ha => halt_decider_max
| Lp1 => loop1_decider 1050000
| Holdout => holdout_checker
end.

Lemma find_tm_spec tm ls:
  find_tm tm ls = true ->
  In tm ls.
Proof.
  induction ls.
  1: cbn; cg.
  unfold find_tm. fold find_tm.
  intro H.
  rewrite shortcut_orb_spec in H.
  rewrite Bool.orb_true_iff in H.
  destruct H as [H|H].
  - left.
    pose proof (tm_eqb_spec tm a).
    destruct (tm_eqb tm a); cg.
  - right.
    apply IHls,H.
Qed.

Lemma tm_holdouts_13_spec:
  forall tm, In tm tm_holdouts_13 -> ~HaltsFromInit Σ Σ0 tm.
Proof.
  intros.
  cbn in H.
  destruct H as [H|H].
  1: subst; apply BB5_Sporadic_Machines.Finned1_nonhalt.
  destruct H as [H|H].
  1: subst; apply BB5_Sporadic_Machines.Finned2_nonhalt.
  destruct H as [H|H].
  1: subst; apply BB5_Sporadic_Machines.Finned3_nonhalt.
  destruct H as [H|H].
  1: subst; apply BB5_Sporadic_Machines.Finned4_nonhalt.
  destruct H as [H|H].
  1: subst; apply BB5_Sporadic_Machines.Finned5_nonhalt.
  destruct H as [H|H].
  1: subst; apply BB5_Sporadic_Machines.Skelet1_nonhalt.
  destruct H as [H|H].
  1: subst; apply BB5_Sporadic_Machines.Skelet10_nonhalt.
  destruct H as [H|H].
  1: subst; apply BB5_Sporadic_Machines.Skelet15_nonhalt.
  destruct H as [H|H].
  1: subst; apply BB5_Sporadic_Machines.Skelet17_nonhalt.
  destruct H as [H|H].
  1: subst; apply BB5_Sporadic_Machines.Skelet26_nonhalt.
  destruct H as [H|H].
  1: subst; apply BB5_Sporadic_Machines.Skelet33_nonhalt.
  destruct H as [H|H].
  1: subst; apply BB5_Sporadic_Machines.Skelet34_nonhalt.
  destruct H as [H|H].
  1: subst; apply BB5_Sporadic_Machines.Skelet35_nonhalt.
  contradiction.
Qed.


Lemma holdout_checker_spec n: HaltDecider_WF n holdout_checker.
Proof.
  unfold HaltDecider_WF.
  intro tm.
  unfold holdout_checker.
  pose proof (find_tm_spec tm tm_holdouts_13) as H.
  destruct (find_tm tm tm_holdouts_13).
  2: trivial.
  specialize (H eq_refl).
  apply tm_holdouts_13_spec,H.
Qed.

Lemma getDecider_spec x:
  HaltDecider_WF (N.to_nat BB5_minus_one) (getDecider x).
Proof.
  destruct x; unfold getDecider.
  - destruct hlen.
    + apply NGramCPS_decider_impl2_spec.
    + apply NGramCPS_decider_impl1_spec.
  - apply NGramCPS_LRU_decider_spec.
  - apply RepWL_ES_decider_spec.
  - apply dfa_nfa_verifier_spec.
  - apply MITM_WDFA_verifier_spec.
  - apply halt_decider_max_spec.
  - apply loop1_decider_WF.
    unfold BB5_minus_one.
    replace (Init.Nat.of_num_uint
  (Number.UIntDecimal
     (Decimal.D1
        (Decimal.D0
           (Decimal.D5 (Decimal.D0 (Decimal.D0 (Decimal.D0 (Decimal.D0 Decimal.Nil))))))))) with
    (N.to_nat 1050000).
    1: lia.
    symmetry.
    apply nat_eqb_N_spec.
    vm_compute.
    reflexivity.
  - apply holdout_checker_spec.
Qed.
