Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import FSets.FMapPositive.

From BusyCoq Require Import BB52Statement.
From BusyCoq Require Import CustomTactics.
From BusyCoq Require Import Prelims.


Fixpoint positive_len(x:positive):nat :=
match x with
| xH => O
| xI x0 => S (positive_len x0)
| xO x0 => S (positive_len x0)
end.

Fixpoint enc_v1(x:positive):positive :=
match x with
| xH => xH
| xI x0 => xI (xI (enc_v1 x0))
| xO x0 => xI (xO (enc_v1 x0))
end.

Lemma enc_v1_eq a1 b1 a2 b2:
  append (enc_v1 a1) (xO b1) = append (enc_v1 a2) (xO b2) ->
  (a1 = a2 /\ b1 = b2).
Proof.
  gd a2.
  induction a1; destruct a2; cbn; intros; cg; invst H.
  1,2: destruct (IHa1 a2 H1).
  all: split; cg.
Qed.

Definition enc_pair(x:positive*positive):positive :=
  let (x1,x2):=x in
  append (enc_v1 (Pos.of_succ_nat (positive_len x1))) (xO (append x1 x2)).

Lemma enc_pair_inj: is_inj enc_pair.
Proof.
  intros x1 x2 H.
  destruct x1 as [a1 b1].
  destruct x2 as [a2 b2].
  unfold enc_pair in H.
  destruct (enc_v1_eq _ _ _ _ H) as [Ha Hb]. clear H.
  assert (positive_len a1 = positive_len a2) by lia. clear Ha.
  gd a2.
  induction a1; destruct a2; cbn; intros; cg;
  invst Hb;
  invst H;
  assert ((a1,b1)=(a2,b2)) by auto 2;
  cg.
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

Definition St_enc(x:St):positive :=
match x with
| St0 => xH
| St1 => xO xH
| St2 => xI xH
| St3 => xO (xO xH)
| St4 => xI (xO xH)
end.

Lemma St_enc_inj: is_inj St_enc.
  intros x1 x2.
  destruct x1,x2; cbn; cg.
Qed.

Definition Σ_eqb(i1 i2:Σ) :=
match i1,i2 with
| Σ0,Σ0 | Σ1,Σ1 => true
| _,_ => false
end.

Lemma Σ_eqb_spec i1 i2:
  if Σ_eqb i1 i2 then i1=i2 else i1<>i2.
Proof.
  destruct i1,i2; cbn; congruence.
Qed.



Definition Σ_enc(x:Σ):positive :=
match x with
| Σ0 => xH
| Σ1 => xO xH
end.

Lemma Σ_enc_inj: is_inj Σ_enc.
  intros x1 x2.
  destruct x1,x2; cbn; cg.
Qed.


Fixpoint listΣ_enc(x:list Σ):positive :=
match x with
| nil => xH
| Σ0::t => xO (listΣ_enc t)
| Σ1::t => xI (listΣ_enc t)
end.

Lemma listΣ_inj: is_inj listΣ_enc.
Proof.
  intros x1 x2 H.
  gd x2.
  induction x1 as [|h1 t1]; destruct x2 as [|h2 t2]; cbn; intros; cg.
  - destruct h2; invst H.
  - destruct h1; invst H.
  - destruct h1,h2; invst H.
    1,2: f_equal; apply IHt1,H1.
Qed.



Lemma map_inj{T1 T2}(f:T1->T2): is_inj f -> is_inj (map f).
Proof.
  intros H x1 x2 H0.
  gd x2.
  induction x1 as [|h1 t1]; destruct x2 as [|h2 t2]; cbn; intros; cg.
  invst H0.
  rewrite (IHt1 _ H3).
  f_equal.
  apply H,H2.
Qed.

Definition listT_enc{T}(f:T->positive)(x:list T):positive :=
  enc_list (map f x).

Lemma listT_enc_inj{T}(f:T->positive): is_inj f -> is_inj (listT_enc f).
Proof.
  intros H x1 x2 H0.
  unfold listT_enc.
  apply (map_inj _ H).
  unfold listT_enc in H0.
  apply enc_list_inj,H0.
Qed.

Definition St_to_nat(x:St):nat:=
match x with
| St0 => 0
| St1 => 1
| St2 => 2
| St3 => 3
| St4 => 4
end.

Lemma St_to_nat_inj: is_inj St_to_nat.
Proof.
  intros x1 x2.
  destruct x1,x2; cbn; cg.
Qed.

Definition St_suc(x:St):St :=
match x with
| St0 => St1
| St1 => St2
| St2 => St3
| St3 => St4
| St4 => St4
end.

Definition St_le(s1 s0:St):Prop :=
  St_to_nat s0 <= St_to_nat s1.

Lemma St_suc_le x:
  St_le (St_suc x) x.
Proof.
  unfold St_le.
  destruct x; cbn; lia.
Qed.

Lemma St_suc_eq x:
  x = (St_suc x) ->
  forall x0, St_le x x0.
Proof.
  destruct x; cbn; cg.
  intros.
  destruct x0; unfold St_le; cbn; lia.
Qed.

Lemma St_suc_neq x:
  x <> (St_suc x) ->
  St_to_nat (St_suc x) = S (St_to_nat x).
Proof.
  destruct x; cbn; cg.
Qed.
