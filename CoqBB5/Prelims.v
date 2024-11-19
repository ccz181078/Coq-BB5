Require Import List.
Require Import ZArith.
Require Import FSets.FMapPositive.

From CoqBB5 Require Import BB52Statement.
From CoqBB5 Require Import CustomTactics.

Definition BB5_minus_one:N := 47176869.

Definition Dir_rev(d:Dir) :=
match d with
| Dneg => Dpos
| Dpos => Dneg
end.


Definition is_inj{T1 T2}(f:T1->T2):=
  forall a b, f a = f b -> a = b.

Lemma fext_inv{A}{B} {f g:A->B}(x:A):
  f = g ->
  f x = g x.
Proof.
  cg.
Qed.

Notation "x &&& y" := (if x then y else false) (at level 80, right associativity).
Notation "x ||| y" := (if x then true else y) (at level 85, right associativity).

Lemma andb_shortcut_spec(a b:bool):
  (a&&&b) = (a&&b)%bool.
Proof.
  reflexivity.
Qed.

Lemma orb_shortcut_spec(a b:bool):
  (a|||b) = (a||b)%bool.
Proof.
  reflexivity.
Qed.


(* A set of encoded things of type T is represented as: `list T * PositiveMap.tree unit`

An encoding function `enc:T->positive` is given which transforms objects of T into keys of
the PositiveMap.tree unit (which can be seen as a set of positive).

When inserting an object in the set, the object is kept as it in `list T` and added using the encoding in the `PositiveMap.tree unit`.
*)

Definition SetOfEncodings T : Type := list T * PositiveMap.tree unit.

Definition set_ins{T}(enc:T->positive)(s: SetOfEncodings T)(x:T):(SetOfEncodings T)*bool :=
  let enc := (enc x) in
  match PositiveMap.find enc (snd s) with
  | None => ((x::fst s, PositiveMap.add enc tt (snd s)),false)
  | Some _ => (s,true)
  end.

Definition set_in{T}(enc:T->positive)(s:SetOfEncodings T)(x:T):Prop :=
  PositiveMap.find (enc x) (snd s) = Some tt.

Definition set_WF{T}(enc:T->positive)(s:SetOfEncodings T):Prop :=
  forall (x:T),
    set_in enc s x <->
    In x (fst s).

Lemma set_ins_spec{T} enc (enc_inj: is_inj enc) s (x:T) s' flag:
  set_WF enc s ->
  set_ins enc s x = (s',flag) ->
  (set_WF enc s' /\
  (flag=true -> (s'=s /\ set_in enc s x))).
Proof.
  unfold set_WF,set_ins,set_in.
  intros.
  destruct (PositiveMap.find (enc x) (snd s)) as [v|] eqn:E.
  - invst H0.
    split.
    1: assumption.
    intros.
    destruct v.
    split; cg.
  - invst H0. clear H0.
    split; intros. 2: cg.
    cbn.
    rewrite (PositiveMapAdditionalFacts.gsspec).
    destruct (PositiveMap.E.eq_dec (enc x0) (enc x)) as [e|e].
    + pose proof (enc_inj _ _ e); subst.
      split; tauto.
    + assert (x<>x0) by cg.
      split; intro.
      * right. rewrite <-H. apply H1.
      * rewrite <-H in H1.
        destruct H1 as [H1|H1]; cg.
Qed.



Lemma empty_set_WF{T}(enc:T->positive):
  set_WF enc (nil, PositiveMap.empty unit).
Proof.
  unfold set_WF.
  intros. cbn.
  split; intro.
  2: contradiction.
  unfold set_in in H.
  rewrite PositiveMap.gempty in H. cg.
Qed.

Definition St_list:= St0::St1::St2::St3::St4::nil.
Definition Σ_list:= Σ0::Σ1::nil.
Definition Dir_list := Dpos::Dneg::nil.

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

Lemma Dir_list_spec:
  forall s, In s Dir_list.
Proof.
  intro s.
  destruct s; cbn; tauto.
Qed.

Definition forallb_St f :=
  forallb f St_list.

Definition forallb_Σ f :=
  forallb f Σ_list.

Definition forallb_Dir f :=
  forallb f Dir_list.

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

Lemma forallb_Dir_spec f:
  forallb_Dir f = true <-> forall s, f s = true.
Proof.
  unfold forallb_Dir.
  rewrite forallb_forall.
  split; intros.
  - apply H,Dir_list_spec.
  - apply H.
Qed.

Definition Dir_eqb(d1 d2:Dir):bool :=
match d1,d2 with
| Dpos,Dpos | Dneg,Dneg => true
| _,_ => false
end.

Lemma Dir_eqb_spec d1 d2:
  if Dir_eqb d1 d2 then d1=d2 else d1<>d2.
Proof.
  destruct d1,d2; cbn; cg.
Qed.

Ltac Dir_eq_dec s1 s2 :=
  eq_dec Dir_eqb_spec Dir_eqb s1 s2.