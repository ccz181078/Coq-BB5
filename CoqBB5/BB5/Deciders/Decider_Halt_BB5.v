Require Import Lia.
Require Import ZArith.

From CoqBB5 Require Import TM.
From CoqBB5 Require Import BB5_Statement.
From CoqBB5 Require Import BB5_Encodings.
From CoqBB5 Require Import Deciders_Common.
From CoqBB5 Require Import Decider_Halt.

Set Warnings "-abstract-large-number".

Definition halt_decider_max := halt_decider 47176870.
Lemma halt_decider_max_spec: HaltDecider_WF (N.to_nat BB5_minus_one) halt_decider_max.
Proof.
  eapply halt_decider_WF.
  unfold BB5_minus_one.
  replace (S (N.to_nat 47176869)) with (N.to_nat 47176870) by lia.
  replace (Init.Nat.of_num_uint
    (Number.UIntDecimal
       (Decimal.D4
          (Decimal.D7
             (Decimal.D1
                (Decimal.D7 (Decimal.D6 (Decimal.D8 (Decimal.D7 (Decimal.D0 Decimal.Nil))))))))))
  with (N.to_nat 47176870).
  1: apply Nat.le_refl.
  symmetry.
  apply nat_eqb_N_spec.
  vm_compute.
  reflexivity.
Qed.

