Require Import Lia.
Require Import List.
Require Import ZArith.

From CoqBB5 Require Import Tactics.
From CoqBB5 Require Import Prelims.
From CoqBB5 Require Import BB5_Encodings.

(* Compute pop_back 0 [ 1 ; 2 ; 3 ; 4 ]. 
   = [0; 1; 2; 3]
   Compute pop_back 0 nil. 
   = nil
*)
Fixpoint pop_back{T}(x:T)(ls:list T):(list T) :=
  match ls with
  | h::t =>
    x::(pop_back h t)
  | nil => nil
  end.

(* Compute pop_back' 0 [ 1 ; 2 ; 3 ; 4 ]. 
   = ([0; 1; 2; 3], 4)
   Compute pop_back' 0 nil. 
   = (nil, 0)
*)
Fixpoint pop_back'{T}(x:T)(ls:list T):(list T)*T :=
  match ls with
  | nil => (nil,x)
  | h :: t => let (a,b):=pop_back' h t in (x::a,b)
  end.

Fixpoint list_nat_sum(ls:list nat):nat :=
  match ls with
  | nil => O
  | h::t => h+(list_nat_sum t)
  end.

Lemma pop_back_len{T} (h:T) t:
  length (pop_back h t) = length t.
Proof.
  gd h.
  induction t; intros; cbn.
  - reflexivity.
  - f_equal; apply IHt.
Qed.

Lemma pop_back__nth_error{T} (h:T) t:
  forall n:nat,
  n<length t ->
  nth_error (pop_back h t) n =
  nth_error (h::t) n.
Proof.
gd h.
induction t; intros.
- cbn in H. lia.
- cbn.
  destruct n.
  1: reflexivity.
  cbn.
  apply IHt. cbn in H. lia.
Qed.

Lemma list_eq__nth_error{T}(ls1 ls2:list T):
  length ls1 = length ls2 ->
  (forall n:nat,
  n<length ls1 ->
  nth_error ls1 n = nth_error ls2 n) ->
  ls1=ls2.
Proof.
  gd ls2.
  induction ls1.
  - intros.
    destruct ls2.
    + reflexivity.
    + cbn in H. cg.
  - intros.
    destruct ls2.
    + cbn in H. cg.
    + assert (a=t) as H1. {
        assert (Some a = Some t) as H1 by (apply (H0 0); cbn; lia).
        cg.
      }
      subst. f_equal.
      cbn in H. invst H.
      eapply IHls1.
      1: assumption.
      intros.
      apply (H0 (S n)).
      cbn. lia.
Qed.

Lemma pop_back'__push_back{T} (h:T) t x2:
  pop_back' h (t ++ x2 :: nil) = (h::t,x2).
Proof.
  gd h.
  induction t; intros; cbn; cg.
  rewrite IHt. reflexivity.
Qed.

Fixpoint enc_list(x:list positive):positive :=
match x with
| nil => xH
| h::t => enc_pair (h,enc_list t)
end.

Lemma enc_list_inj: is_inj enc_list.
Proof.
  intros x1 x2 H.
  gd x2.
  induction x1 as [|h1 t1]; destruct x2 as [|h2 t2]; intros; cg.
  - cbn in H. destruct ((Pos.of_succ_nat (positive_len h2))); cbn in H; cg.
  - cbn in H. destruct ((Pos.of_succ_nat (positive_len h1))); cbn in H; cg.
  - epose proof (enc_pair_inj _ _ H).
    invst H0.
    f_equal.
    apply IHt1; assumption.
Qed.