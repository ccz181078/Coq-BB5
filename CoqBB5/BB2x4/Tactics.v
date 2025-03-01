Require Import Logic.FunctionalExtensionality.
From CoqBB2x4 Require Import BB2x4_Statement.

Ltac invst H := inversion H; subst.
Ltac ctor := constructor.
Ltac ector := econstructor.
Ltac fext := apply functional_extensionality; intro.
Ltac gd x := generalize dependent x.
Ltac cg := try congruence.

Ltac eq_dec eqb_spec eqb s1 s2 :=
  pose proof (eqb_spec s1 s2);
  destruct (eqb s1 s2).

Lemma St_eqb_spec s1 s2:
  if St_eqb s1 s2 then s1=s2 else s1<>s2.
Proof.
  destruct s1,s2; cbn; congruence.
Qed.

Ltac St_eq_dec s1 s2 :=
  eq_dec St_eqb_spec St_eqb s1 s2.

Lemma ffx_eq_x_inj{A}:
  forall f:A->A,
  (forall x:A, f (f x) = x) ->
  forall x y:A, f x = f y -> x = y.
Proof.
  intros.
  assert ((f (f x)) = (f (f y))) as H1. {
    rewrite H0,H. reflexivity.
  }
  rewrite H,H in H1.
  apply H1.
Qed.

Ltac ff_inj RR H := pose proof (ffx_eq_x_inj _ RR _ _ H); subst.

Ltac clr_eqrefl:=
  repeat match goal with
  | H: ?A = ?A |- _ => clear H
  end.

Ltac clr_dup:=
  repeat match goal with
  | H:?A, H':?A |- _ => clear H'
  end.

Ltac clrs:=
  clr_eqrefl; clr_dup.

Ltac destruct_and :=
  match goal with
  | H:?A/\?B |- _ => destruct H
  end.