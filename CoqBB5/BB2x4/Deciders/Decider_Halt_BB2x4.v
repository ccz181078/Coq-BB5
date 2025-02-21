Require Import Lia.
Require Import ZArith.

From CoqBB2x4 Require Import TM.
From CoqBB2x4 Require Import BB2x4_Statement.
From CoqBB2x4 Require Import BB2x4_Encodings.
From CoqBB2x4 Require Import Deciders_Common.
From CoqBB2x4 Require Import Decider_Halt.

Set Warnings "-abstract-large-number".

Definition halt_decider_max := halt_decider 3932964.
Lemma halt_decider_max_spec: HaltDecider_WF (N.to_nat BB2x4_minus_one) halt_decider_max.
Proof.
  eapply halt_decider_WF.
  unfold BB2x4_minus_one.
  replace (S (N.to_nat 3932963)) with (N.to_nat 3932964) by lia.
  replace (Init.Nat.of_num_uint
  (Number.UIntDecimal
     (Decimal.D3
        (Decimal.D9
           (Decimal.D3 (Decimal.D2 (Decimal.D9 (Decimal.D6 (Decimal.D4 Decimal.Nil)))))))))
  with (N.to_nat 3932964).
  1: apply Nat.le_refl.
  symmetry.
  apply nat_eqb_N_spec.
  vm_compute.
  reflexivity.
Qed.