From BusyCoq Require Import BB52Statement.
From BusyCoq Require Import ListTape.
From BusyCoq Require Import Decider_RepWL.

From BusyCoq Require Import CustomTactics.

Definition halt_time_verifier(tm:TM Σ)(n:nat):bool :=
  match ListES_Steps tm n {| ListTape.l := nil; ListTape.r := nil; ListTape.m := Σ0; ListTape.s := St0 |} with
  | Some {| ListTape.l:=_; ListTape.r:=_; ListTape.m :=m0; ListTape.s :=s0 |} =>
    match tm s0 m0 with
    | None => true
    | _ => false
    end
  | None => false
  end.

Lemma halt_time_verifier_spec tm n:
  halt_time_verifier tm n = true ->
  TM_CoqBB5.HaltsAt _ tm n (InitES Σ Σ0).
Proof.
  unfold halt_time_verifier,TM_CoqBB5.HaltsAt.
  intro H.
  pose proof (ListES_Steps_spec tm n {| ListTape.l := nil; ListTape.r := nil; ListTape.m := Σ0; ListTape.s := St0 |}).
  destruct (ListES_Steps tm n {| ListTape.l := nil; ListTape.r := nil; ListTape.m := Σ0; ListTape.s := St0 |}).
  2: cg.
  rewrite ListES_toES_O in H0.
  eexists.
  split.
  - apply H0.
  - destruct l0 as [l0 r0 m0 s0].
    cbn.
    destruct (tm s0 m0); cg.
Qed.

Definition BB:N := 47176869.

Fixpoint nat_eqb_N(n:nat)(m:N) :=
match n,m with
| O,N0 => true
| S n0,Npos _ => nat_eqb_N n0 (N.pred m)
| _,_ => false
end.

Lemma nat_eqb_N_spec n m :
  nat_eqb_N n m = true -> n = N.to_nat m.
Proof.
  gd m.
  induction n; intros.
  - cbn in H.
    destruct m0; cbn; cg.
  - destruct m0.
    + cbn in H. cg.
    + cbn in H.
      specialize (IHn (Pos.pred_N p) H). lia.
Qed.


Definition halt_decider_max := halt_decider 47176870.
Lemma halt_decider_max_spec: HaltDecider_WF (N.to_nat BB) halt_decider_max.
Proof.
  eapply halt_decider_WF.
  unfold BB.
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
Time Qed.

Definition BB5_champion := (makeTM BR1 CL1 CR1 BR1 DR1 EL0 AL1 DL1 HR1 AL0).

Lemma BB5_lower_bound:
  exists tm,
  TM_CoqBB5.HaltsAt _ tm (N.to_nat BB) (InitES Σ Σ0).
Proof.
  exists BB5_champion.
  apply halt_time_verifier_spec.
  vm_compute.
  reflexivity.
Time Qed.


Definition decider0 := HaltDecider_nil.
Definition decider1 := halt_decider 130.
Definition decider2 := (loop1_decider 130 (1::2::4::8::16::32::64::128::256::512::nil)).

Definition decider3 := (NGramCPS_decider_impl2 1 1 100).
Definition decider4 := (NGramCPS_decider_impl2 2 2 200).
Definition decider5 := (NGramCPS_decider_impl2 3 3 400).
Definition decider6 := (NGramCPS_decider_impl1 2 2 2 1600).
Definition decider7 := (NGramCPS_decider_impl1 2 3 3 1600).

Definition decider8 := (loop1_decider 4100 (1::2::4::8::16::32::64::128::256::512::1024::2048::4096::nil)).

Definition decider9 := (NGramCPS_decider_impl1 4 2 2 600).
Definition decider10 := (NGramCPS_decider_impl1 4 3 3 1600).
Definition decider11 := (NGramCPS_decider_impl1 6 2 2 3200).
Definition decider12 := (NGramCPS_decider_impl1 6 3 3 3200).
Definition decider13 := (NGramCPS_decider_impl1 8 2 2 1600).
Definition decider14 := (NGramCPS_decider_impl1 8 3 3 1600).

Lemma decider2_WF: HaltDecider_WF (N.to_nat BB) decider2.
Proof.
  apply loop1_decider_WF.
  unfold BB.
  lia.
Qed.

Lemma root_q_WF:
  SearchQueue_WF (N.to_nat BB) root_q root.
Proof.
  apply SearchQueue_init_spec,root_WF.
Qed.

Definition root_q_upd1:=
  (SearchQueue_upd root_q decider2).

Lemma root_q_upd1_WF:
  SearchQueue_WF (N.to_nat BB) root_q_upd1 root.
Proof.
  apply SearchQueue_upd_spec.
  - apply root_q_WF.
  - apply decider2_WF.
Qed.

Definition first_trans_is_R(x:TNF_Node):bool :=
  match x.(TNF_tm) St0 Σ0 with
  | Some {| nxt:=_; dir:=Dpos; out:=_ |} => true
  | _ => false
  end.

Definition root_q_upd1_simplified:SearchQueue:=
  (filter first_trans_is_R (fst root_q_upd1), nil).

Lemma TM_rev_upd'_TM0 s0 o0:
  (TM_upd' (TM0) St0 Σ0 (Some {| nxt := s0; dir := Dneg; out := o0 |})) =
  (TM_rev Σ (TM_upd' (TM0) St0 Σ0 (Some {| nxt := s0; dir := Dpos; out := o0 |}))).
Proof.
  repeat rewrite TM_upd'_spec.
  fext. fext.
  unfold TM_upd,TM_rev,TM0.
  St_eq_dec x St0.
  - Σ_eq_dec x0 Σ0; cbn; reflexivity.
  - cbn; reflexivity.
Qed.

Lemma root_q_upd1_simplified_WF:
  SearchQueue_WF (N.to_nat BB) root_q_upd1_simplified root.
Proof.
  pose proof (root_q_upd1_WF).
  cbn in H.
  destruct H as [Ha Hb].
  cbn.
  split.
  - intros x H0.
    pose proof (Ha x). tauto.
  - intro H0. apply Hb.
    intros x H1.
    destruct H1 as [H1|[H1|[H1|[H1|[H1|[H1|[H1|[H1|H1]]]]]]]]; try (specialize (H0 x); tauto).
    1,2,3,4:
      clear Ha; clear Hb;
      destruct x as [tm cnt ptr];
      cbn; invst H1;
      rewrite TM_rev_upd'_TM0;
      eapply HaltTimeUpperBound_LE_rev_InitES.
    1: eassert (H2:_) by (apply (H0 {|
             TNF_tm := TM_upd' (TM0) St0 Σ0 (Some {| nxt := St0; dir := Dpos; out := Σ0 |});
             TNF_cnt := 9;
             TNF_ptr := St1
           |}); tauto); apply H2.
    1: eassert (H2:_) by (apply (H0 {|
             TNF_tm := TM_upd' (TM0) St0 Σ0 (Some {| nxt := St0; dir := Dpos; out := Σ1 |});
             TNF_cnt := 9;
             TNF_ptr := St1
           |}); tauto); apply H2.
    1: eassert (H2:_) by (apply (H0 {|
             TNF_tm := TM_upd' (TM0) St0 Σ0 (Some {| nxt := St1; dir := Dpos; out := Σ0 |});
             TNF_cnt := 9;
             TNF_ptr := St2
           |}); tauto); apply H2.
    1: eassert (H2:_) by (apply (H0 {|
             TNF_tm := TM_upd' (TM0) St0 Σ0 (Some {| nxt := St1; dir := Dpos; out := Σ1 |});
             TNF_cnt := 9;
             TNF_ptr := St2
           |}); tauto); apply H2.
Qed.

Fixpoint length_tailrec0{T}(ls:list T)(n:N):N :=
match ls with
| nil => n
| h::t => length_tailrec0 t (N.succ n)
end.
Definition length_tailrec{T}(ls:list T):N := length_tailrec0 ls 0.


Inductive DeciderType :=
| NG(hlen len:nat)
| NG_LRU(len:nat)
| RWL(len m:nat)
| DNV(n:nat)(f:nat->Σ->nat)
| WA(max_d:BinNums.Z)(n_l:nat)(f_l:nat->Σ->(nat*BinNums.Z))(n_r:nat)(f_r:nat->Σ->(nat*BinNums.Z))
| Ha
| Lp1
| Holdout.


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
| Lp1 => loop1_decider 1050000 (4096::8192::16384::32768::65536::131072::262144::524288::nil)
| Holdout => holdout_checker
end.

Lemma getDecider_spec x:
  HaltDecider_WF (N.to_nat BB) (getDecider x).
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
    unfold BB.
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