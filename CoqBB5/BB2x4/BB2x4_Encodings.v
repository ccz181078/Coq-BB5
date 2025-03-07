Require Import List.
Require Import ZArith.
Require Import Lia.
Require Import FSets.FMapPositive.

From CoqBB2x4 Require Import BB2x4_Statement.
From CoqBB2x4 Require Import Tactics.
From CoqBB2x4 Require Import Prelims.

Definition St_list:= St0::St1::nil.
Definition Σ_list:= Σ0::Σ1::Σ2::Σ3::nil.

Definition BB2x4_minus_one:N := 3932963.

Lemma St_list_spec:
  forall s, In s St_list.
Proof.
  intro s.
  destruct s; cbn; tauto.
Qed.

Lemma Σ_list_spec:
  forall s, In s Σ_list.
Proof.
  intro s.
  destruct s; cbn; tauto.
Qed.

Definition forallb_St f :=
  forallb f St_list.

Definition forallb_Σ f :=
  forallb f Σ_list.

Lemma forallb_St_spec f:
  forallb_St f = true <-> forall s, f s = true.
Proof.
  unfold forallb_St.
  rewrite forallb_forall.
  split; intros.
  - apply H,St_list_spec.
  - apply H.
Qed.

Lemma forallb_Σ_spec f:
  forallb_Σ f = true <-> forall s, f s = true.
Proof.
  unfold forallb_Σ.
  rewrite forallb_forall.
  split; intros.
  - apply H,Σ_list_spec.
  - apply H.
Qed.

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



end.

Lemma St_enc_inj: is_inj St_enc.
  intros x1 x2.
  destruct x1,x2; cbn; cg.
Qed.


Lemma Σ_eqb_spec i1 i2:
  if Σ_eqb i1 i2 then i1=i2 else i1<>i2.
Proof.
  destruct i1,i2; cbn; congruence.
Qed.



Definition Σ_enc(x:Σ):positive :=
match x with
| Σ0 => xH
| Σ1 => xO xH
| Σ2 => xI xH
| Σ3 => xO (xO xH)
end.

Lemma Σ_enc_inj: is_inj Σ_enc.
  intros x1 x2.
  destruct x1,x2; cbn; cg.
Qed.


Fixpoint listΣ_enc(x:list Σ):positive :=
match x with
| nil => xH
| Σ0::t => xO (xO (listΣ_enc t))
| Σ1::t => xI (xO (listΣ_enc t))
| Σ2::t => xO (xI (listΣ_enc t))
| Σ3::t => xI (xI (listΣ_enc t))
end.

Lemma listΣ_inj: is_inj listΣ_enc.
Proof.
  intros x1 x2 H.
  gd x2.
  induction x1 as [|h1 t1]; destruct x2 as [|h2 t2]; cbn; intros; cg.
  - destruct h2; invst H.
  - destruct h1; invst H.
  - destruct h1,h2; invst H.
    all: f_equal; apply IHt1,H1.
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
end.

Lemma St_to_nat_inj: is_inj St_to_nat.
Proof.
  intros x1 x2.
  destruct x1,x2; cbn; cg.
Qed.

Definition St_suc(x:St):St :=
match x with
| St0 => St1
| St1 => St1
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

Definition St_to_N(s1:St):N :=
match s1 with
| St0 => 1
| St1 => 2
end.

Definition Dir_to_N(d1:Dir):N :=
match d1 with
| Dpos => 1
| Dneg => 0
end.

Definition Σ_to_N(o1:Σ):N :=
match o1 with
| Σ0 => 0
| Σ1 => 1
| Σ2 => 2
| Σ3 => 3
end.

Definition Trans_to_N(tr:Trans Σ):list (N*N) :=
let (s1,d1,o1):=tr in
((St_to_N s1,6)::(Σ_to_N o1,2)::(Dir_to_N d1,2)::nil)%N.

Definition option_Trans_to_N(tr:option (Trans Σ)):list (N*N) :=
match tr with
| None =>
  ((0,6)::(Σ_to_N Σ1,2)::(Dir_to_N Dpos,2)::nil)%N
| Some tr => Trans_to_N tr
end.

Fixpoint listStΣ_enc(x:list (St*Σ)):positive:=
match x with
| nil => xH
| (St0,Σ0)::t => (listStΣ_enc t)~0~0~0
| (St0,Σ1)::t => (listStΣ_enc t)~1~0~0
| (St0,Σ2)::t => (listStΣ_enc t)~0~1~0
| (St0,Σ3)::t => (listStΣ_enc t)~1~1~0
| (St1,Σ0)::t => (listStΣ_enc t)~0~0~1
| (St1,Σ1)::t => (listStΣ_enc t)~1~0~1
| (St1,Σ2)::t => (listStΣ_enc t)~0~1~1
| (St1,Σ3)::t => (listStΣ_enc t)~1~1~1
end.

Lemma listStΣ_enc_inj: is_inj listStΣ_enc.
Proof.
  intros x1 x2 H.
  gd x2.
  induction x1 as [|h1 t1]; destruct x2 as [|h2 t2]; cbn; intros; cg.
  - destruct h2 as [s i]; destruct s,i; invst H.
  - destruct h1 as [s i]; destruct s,i; invst H.
  - destruct h1 as [s1 i1]; destruct s1,i1;
    destruct h2 as [s2 i2]; destruct s2,i2;
    invst H;
    f_equal; apply IHt1,H1.
Qed.

Definition Dir_enc(d:Dir):=
match d with
| Dpos => xI xH
| Dneg => xH
end.

Lemma Dir_enc_inj: is_inj Dir_enc.
Proof.
  intros x1 x2 H.
  destruct x1,x2; cbn in H; cg.
Qed.

Definition bool_enc(x:bool):=
  if x then xI xH else xH.

Lemma bool_enc_inj: is_inj bool_enc.
Proof.
  intros x1 x2 H.
  destruct x1,x2; cbn in H; cg.
Qed.