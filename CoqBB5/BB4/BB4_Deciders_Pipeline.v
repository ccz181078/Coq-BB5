Require Import ZArith.
Require Import Lia.
Require Import List.
Require Export FSets.FMapPositive.

From CoqBB4 Require Import BB4_Statement.
From CoqBB4 Require Import BB4_Deciders_Generic.
From CoqBB4 Require Import List_Tape.
From CoqBB4 Require Import TNF.
From CoqBB4 Require Import Tactics.
From CoqBB4 Require Import TM.
From CoqBB4 Require Import Prelims.
From CoqBB4 Require Import BB4_Encodings.

From CoqBB4 Require Import Deciders_Common.
From CoqBB4 Require Import Decider_Halt.
From CoqBB4 Require Import Decider_Halt_BB4.
From CoqBB4 Require Import Decider_Loop.
From CoqBB4 Require Import Decider_NGramCPS.
From CoqBB4 Require Import Decider_RepWL.

Set Warnings "-abstract-large-number".

(* Definition decider0 := HaltDecider_nil.
Definition decider1 := halt_decider 130. *)
Definition decider2 := ((loop1_decider 107),LOOP1_params_107).

Definition decider3 := ((NGramCPS_decider_impl2 1 1 100),NGRAM_CPS_IMPL2_params_1_1_100).
Definition decider4 := ((NGramCPS_decider_impl2 2 2 200),NGRAM_CPS_IMPL2_params_2_2_200).
Definition decider5 := ((NGramCPS_decider_impl2 3 3 400),NGRAM_CPS_IMPL2_params_3_3_400).
Definition decider6 := ((NGramCPS_decider_impl1 2 2 2 1600),NGRAM_CPS_IMPL1_params_2_2_2_1600).
Definition decider7 := ((NGramCPS_decider_impl1 2 3 3 1600),NGRAM_CPS_IMPL1_params_2_3_3_1600).

(* Definition decider8 := ((loop1_decider 4100),LOOP1_params_4100). *) (* unused *)

Definition decider9 := ((NGramCPS_decider_impl1 4 2 2 600),NGRAM_CPS_IMPL1_params_4_2_2_600).
Definition decider10 := ((NGramCPS_decider_impl1 4 3 3 1600),NGRAM_CPS_IMPL1_params_4_3_3_1600).
Definition decider11 := ((NGramCPS_decider_impl1 6 2 2 3200),NGRAM_CPS_IMPL1_params_6_2_2_3200).
Definition decider12 := ((NGramCPS_decider_impl1 6 3 3 3200),NGRAM_CPS_IMPL1_params_6_3_3_3200).
Definition decider13 := ((NGramCPS_decider_impl1 8 2 2 1600),NGRAM_CPS_IMPL1_params_8_2_2_1600).
Definition decider14 := ((NGramCPS_decider_impl1 8 3 3 1600),NGRAM_CPS_IMPL1_params_8_3_3_1600).

Definition decider15 := ((NGramCPS_LRU_decider 2 2 10000),NGRAM_CPS_LRU_params_2_2_10000).
Definition decider16 := ((NGramCPS_decider_impl1 10 4 4 10000),NGRAM_CPS_IMPL1_params_10_4_4_10000).

Definition decider17 := ((RepWL_ES_decider 4 3 320 10000),REPWL_params_4_3_320_10000).

Definition decider_all :=
  (HaltDecider_list
(decider2::decider3::decider4::decider5::decider6::decider7::
decider9::decider10::
decider11::decider12::
decider13::decider14::
decider15::
decider16::
decider17::nil)).

Lemma decider2_WF: HaltDecider_WF (N.to_nat BB4_minus_one) (fst decider2).
Proof.
  apply loop1_decider_WF.
  unfold BB4_minus_one.
  lia.
Qed.

Lemma decider_all_spec: HaltDeciderWithIdentifier_WF (N.to_nat BB4_minus_one) decider_all.
Proof.
unfold decider_all,HaltDecider_list.
  repeat apply HaltDecider_cons_spec.
  all: try apply NGramCPS_decider_impl2_spec.
  all: try apply NGramCPS_decider_impl1_spec.
  - apply decider2_WF.
  - apply NGramCPS_LRU_decider_spec.
  - apply RepWL_ES_decider_spec.
  - unfold HaltDecider_nil,HaltDeciderWithIdentifier_WF.
    intro. simpl. trivial.
Qed.