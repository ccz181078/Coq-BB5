Require Export List.
Require Export ZArith.
Require Export Logic.FunctionalExtensionality.
Require Export Lia.
Require Export FSets.FMapPositive.

From CoqBB5 Require Export BB52Statement.
From CoqBB5 Require Export TNF.
From CoqBB5 Require Export ListTape.
From CoqBB5 Require Export TM.
From CoqBB5 Require Export Prelims.
From CoqBB5 Require Export Encodings.
From CoqBB5 Require Export CustomTactics.
From CoqBB5 Require Export Decider_Pipeline.


From CoqBB5 Require Export Deciders.Decider_Loop.
From CoqBB5 Require Export Deciders.Decider_NGramCPS.


From CoqBB5 Require Export Deciders_CustomParameters.Decider_Loop_CustomParameters.
From CoqBB5 Require Export Deciders_CustomParameters.Decider_NGramCPS_CustomParameters.
From CoqBB5 Require Export Deciders_CustomParameters.Decider_Verifier_FAR_CustomParameters.
From CoqBB5 Require Export Deciders_CustomParameters.Decider_Verifier_FAR_MITM_WDFA_CustomParameters.
From CoqBB5 Require Export Deciders_CustomParameters.Decider_RepWL_CustomParameters.
From CoqBB5 Require Export Deciders_CustomParameters.Decider_Halt_CustomParameters.



From CoqBB5 Require Export Sporadic_NonHalt.


Definition check_tms(ls:list ((TM Σ)*DeciderType)):=
  map (fun (x:(TM Σ)*DeciderType)=> let (tm,d):=x in getDecider d tm) ls.

(*
Compute (length tm_WA).
Time Definition check_res := Eval vm_compute in (check_tms ((tm_WA))).
Compute (filter (fun x => match x with Result_NonHalt => false | _ => true end) check_res).
Compute check_res.
*)


Definition tm_list :=
  tm_RWL::
  tm_NG0::tm_NG2::tm_NG3::tm_NG4::tm_NG5::tm_NG6::tm_NG7::tm_NG_ge8::
  tm_Ha::
  tm_Lp1::
  tm_NG_LRU::
  tm_NG0'::tm_RWL'::
  tm_DNV::tm_WA::
  (map (fun tm => (tm,Holdout)) tm_holdouts_13)::
  nil.


Definition TM_enc(tm:TM Σ):positive :=
  match TM_to_N tm with
  | N0 => xH
  | Npos v => Pos.succ v
  end.

Fixpoint TM_ins_all(ls:list ((TM Σ)*DeciderType))(mp:PositiveMap.tree DeciderType):PositiveMap.tree DeciderType :=
match ls with
| nil => mp
| (h1,h2)::t => TM_ins_all t (PositiveMap.add (TM_enc h1) h2 mp)
end.

Fixpoint TM_ins_all'(ls:list (list ((TM Σ)*DeciderType)))(mp:PositiveMap.tree DeciderType):PositiveMap.tree DeciderType :=
match ls with
| nil => mp
| h::t => TM_ins_all' t (TM_ins_all h mp)
end.

Definition tm_decider_table :=
  Eval vm_compute in (TM_ins_all' tm_list (PositiveMap.empty DeciderType)).

Definition table_based_decider(tm:TM Σ):HaltDecideResult :=
  match PositiveMap.find (TM_enc tm) tm_decider_table with
  | None => Result_Unknown
  | Some d => getDecider d tm
  end.

Lemma table_based_decider_spec: HaltDecider_WF (N.to_nat BB5_minus_one) table_based_decider.
Proof.
  unfold HaltDecider_WF,table_based_decider.
  intros tm.
  destruct (PositiveMap.find (TM_enc tm) tm_decider_table).
  2: trivial.
  apply getDecider_spec.
Qed.

Definition NF_decider(dec:HaltDecider)(tm:TM Σ):HaltDecideResult :=
  match dec (TM_to_NF tm) with
  | Result_NonHalt => Result_NonHalt
  | _ => Result_Unknown
  end.

Lemma NF_decider_spec dec n:
  HaltDecider_WF n dec ->
  HaltDecider_WF n (NF_decider dec).
Proof.
  unfold HaltDecider_WF,NF_decider.
  intro H.
  intro tm.
  specialize (H (TM_to_NF tm)).
  destruct (dec (TM_to_NF tm)).
  1,3: trivial.
  unfold HaltsFromInit.
  unfold HaltsFromInit in H.
  rewrite <-NonHalt_iff.
  rewrite <-NonHalt_iff in H.
  rewrite <-TM_to_NF_spec in H.
  apply H.
Qed.

Definition decider_all :=
  (HaltDecider_list
(decider2::decider3::decider4::decider5::decider6::decider7::decider8::
decider9::decider10::
decider11::decider12::
decider13::decider14::
table_based_decider::
(NF_decider table_based_decider)::
nil)).

Lemma decider_all_spec: HaltDecider_WF (N.to_nat BB5_minus_one) decider_all.
Proof.
  unfold decider_all,HaltDecider_list.
  repeat apply HaltDecider_cons_spec.
  all: try apply NGramCPS_decider_impl2_spec.
  all: try apply NGramCPS_decider_impl1_spec.
  - apply decider2_WF.
  - apply loop1_decider_WF.
    unfold BB5_minus_one. lia.
  - apply table_based_decider_spec.
  - apply NF_decider_spec,table_based_decider_spec.
  - unfold HaltDecider_nil,HaltDecider_WF.
    intro. trivial.
Qed.

Lemma SearchQueue_WF_implies_TNF_Node_HTUB BB (q : SearchQueue) root :
  (  let (q1, q2) := q in
     (forall x : TNF_Node, In x (q1 ++ q2) -> TNF_Node_HTUB BB x)) ->
  SearchQueue_WF BB q root ->
  TNF_Node_HTUB BB root.
Proof.
  intros. red in H0.
  destruct q as [q1 q2].
  eapply H0.
  eauto.
Qed.

Definition q_suc:SearchQueue->SearchQueue := (fun x => SearchQueue_upds x decider_all 20).

Lemma q_200_WF_gen :
  forall t : TNF_Node,
    TNF_Node_WF t -> forall n : nat, SearchQueue_WF (N.to_nat BB5_minus_one) (Nat.iter n q_suc (SearchQueue_init t)) t.
Proof.
  intros root root_wf n.
  induction n.
  - apply SearchQueue_init_spec. assumption. 
  - rewrite Nat.iter_succ. 
    apply SearchQueue_upds_spec.
    + exact IHn.
    + apply decider_all_spec.
Qed.

Lemma iter_S{A}(f:A->A)(x x0:A) n:
  x0 = Nat.iter n f x ->
  f x0 = Nat.iter (S n) f x.
Proof.
  intro H.
  rewrite H.
  reflexivity.
Qed.