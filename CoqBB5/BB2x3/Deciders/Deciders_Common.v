Require Import ZArith.
Require Import List.

From CoqBB2x3 Require Import BB2x3_Statement.
From CoqBB2x3 Require Import BB2x3_Deciders_Generic.
From CoqBB2x3 Require Import TM.


Section Deciders_Common.

Hypothesis BB: nat.

Inductive HaltDecideResult :=
| Result_Halt(s:St)(i:Σ)
| Result_NonHalt
| Result_Unknown
.

Definition HaltDecider := TM Σ -> HaltDecideResult.
Definition HaltDeciderWithIdentifier := TM Σ -> HaltDecideResult*DeciderIdentifier.

Definition MakeHaltDeciderWithIdentifier (f_and_id:HaltDecider*DeciderIdentifier):HaltDeciderWithIdentifier :=
  fun tm => ((fst f_and_id) tm, (snd f_and_id)).

Definition HaltDecider_WF(f:HaltDecider) :=
  forall tm,
    match f tm with
    | Result_Halt s i => exists n t, HaltsAt _ tm n (InitES Σ Σ0) /\ Steps _ tm n (InitES Σ Σ0) (s,t) /\ t Z0 = i /\ n<=BB
    | Result_NonHalt => ~HaltsFromInit Σ Σ0 tm
    | Result_Unknown => True
    end.

Definition HaltDeciderWithIdentifier_WF(g:HaltDeciderWithIdentifier) :=
  forall tm,
    match fst (g tm) with
    | Result_Halt s i => exists n t, HaltsAt _ tm n (InitES Σ Σ0) /\ Steps _ tm n (InitES Σ Σ0) (s,t) /\ t Z0 = i /\ n<=BB
    | Result_NonHalt => ~HaltsFromInit Σ Σ0 tm
    | Result_Unknown => True
    end. 

Definition HaltDecider_cons (f:HaltDecider) (decider_id: DeciderIdentifier) (g:HaltDeciderWithIdentifier):HaltDeciderWithIdentifier :=
  fun tm =>
    let res := f tm in
      match res with
      | Result_Unknown => g tm
      | _ => (res,decider_id)
      end.

Lemma HaltDecider_cons_spec (f:HaltDecider) (g:HaltDeciderWithIdentifier):
  forall decider_id,
    HaltDecider_WF f ->
    HaltDeciderWithIdentifier_WF g ->
    HaltDeciderWithIdentifier_WF (HaltDecider_cons f decider_id g).
Proof.
  intro decider_id.
  intros Hf Hg tm.
  specialize (Hf tm).
  specialize (Hg tm).
  unfold HaltDecider_cons.
  destruct (f tm); auto 1.
Qed.

Definition HaltDecider_nil:HaltDeciderWithIdentifier := fun _ => (Result_Unknown, DECIDER_NIL).

Fixpoint HaltDecider_list(f:list (HaltDecider*DeciderIdentifier)):HaltDeciderWithIdentifier :=
  match f with
  | nil => HaltDecider_nil
  | h::t => HaltDecider_cons (fst h) (snd h) (HaltDecider_list t)
  end.

End Deciders_Common.