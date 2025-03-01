Require Import Lia.
Require Import List.
Require Import ZArith.

From CoqBB2 Require Import TM.
From CoqBB2 Require Import BB2_Statement.
From CoqBB2 Require Import Tactics.
From CoqBB2 Require Import TNF.
From CoqBB2 Require Import List_Tape.
From CoqBB2 Require Import Prelims.
From CoqBB2 Require Import BB2_Encodings.
From CoqBB2 Require Import Deciders_Common.

(* Begin: Loop decider implementation *)

(** Loop-finder algorithm: loop detection.

  .       .       h1
  .       h1      x
  h1  ->  x   ->  x
  .       .       h0
  .       h0      x
  h0      x       x

  This recursive algorithm rewinds the history of configurations and tape positions n0 times where 
  `h0` and `h1` are always distant of n0 steps with n0 the initial value of parameter `n`.

  The algorithm continues rewinding until `h1` is record breaking (i.e. no cells to the left or right has ever been visited before).

  At each step, the algorithm checks that `h0` and `h1` have the same state and read symbol.
  If not, false is returned as it is not a loop.

  Otherwise a loop is detected and :

  - if h0 and h1 are at same position, the loop is a standard loop (i.e. same configuration reached twice)
  - if h0 and h1 are not at same position, the loop is a translated loop (i.e. repeating motif translated on tape)

  Note that this loop-detection algorithm is different from historically-developed algorithms that look at the entire tape rather than considering the history of state-symbol pairs.

  Args:
    - h0: ListES*Z, configuration and tape head position, initially it is the last reached configuration (see `loop1_decider0`)
    - h1: ListES*Z, configuration and tape head position n0 steps before `h0` where n0 is the initial value of parameter `n`
    - ls0: list (ListES*Z), history of visited configurations and tape head positions before h0 (excluded)
    - ls1: list (ListES*Z), history of visited configurations and tape head positions before h1 (excluded)
    - n: nat, initial value of the number of steps separating h0 from h1 also corresponds to the minimum amount of history rewinds to perform
    - dpos: Z, initial tape head position difference between h0 and h1, this parameter is useful to detect translated loops
*)

Fixpoint verify_loop1(h0 h1:ListES*Z)(ls0 ls1:list (ListES*Z))(n:nat)(dpos:Z):bool :=
  let (es0,d0):=h0 in
  let (es1,d1):=h1 in
  St_eqb es0.(s) es1.(s) &&&
  Σ_eqb es0.(m) es1.(m) &&&
  (
    match n with
    | O =>
      match dpos with
      | Z0 => Z.eqb d1 d0
      | Zpos _ =>
        match es1.(r) with
        | nil => Z.ltb d1 d0
        | _ => false
        end
      | Zneg _ =>
        match es1.(l) with
        | nil => Z.ltb d0 d1
        | _ => false
        end
      end
    | _ => false
    end |||
    match ls0,ls1 with
    | h0'::ls0',h1'::ls1' =>
      verify_loop1 h0' h1' ls0' ls1' (Nat.pred n) dpos
    | _,_ => false
    end
  ).

(** Loop-finder algorithm: main body.

  The algorithm considers three configurations `h0`, `h1`, `h2` each separated by n+1 execution steps. E.g. for n=1:
        h2
        .
        .
        h1
        .
        .
        h0

  Where `h0` is constant, the last reached configuration in `loop1_decider0`.

  If configurations `h0`, `h1`, `h2` have same state and read symbol then the algorithm verifies whether
  a loop has been met (see `verify_loop1`).

  Otherwise, the algorithm proceeds to the next `n` (until histories are empty).

  Args:
    - h0: ListES*Z, last reached configuration (see `loop1_decider0`) and tape head position
    - h1: ListES*Z, configuration and tape head position (n+1) steps before `h0`
    - h2: ListES*Z, configuration and tape head position (n+1) steps before `h1`
    - ls0: list (ListES*Z), history of visited configurations and tape head positions before h0 (excluded)
    - ls1: list (ListES*Z), history of visited configurations and tape head positions before h1 (excluded)
    - ls2: list (ListES*Z), history of visited configurations and tape head positions before h2 (excluded)
    - n: nat, n+1 represents the number of steps separating h0 from h1 and h1 from h2

  Returns true iff a loop is detected for the triple  `h0`, `h1`, `h2`.
*)

Fixpoint find_loop1(h0 h1 h2:ListES*Z)(ls0 ls1 ls2:list (ListES*Z))(n:nat){struct ls1}:bool :=
  (
    (let (es0,d0):=h0 in
    let (es1,d1):=h1 in
    St_eqb es0.(s) es1.(s) &&&
    let (es2,d2):=h2 in
    St_eqb es0.(s) es2.(s) &&&

    Σ_eqb es0.(m) es1.(m) &&&
    Σ_eqb es0.(m) es2.(m) &&&

    (verify_loop1 h0 h1 ls0 ls1 (S n) (d0-d1)))
  ) |||

  match ls2,ls1 with
  | h3::h2'::ls2',h1'::ls1' =>
    find_loop1 h0 h1' h2' ls0 ls1' ls2' (S n)
  | _,_ => false
  end.


(** Loop-finder algorithm entrypoint.

  Args:
    - h0: ListES*Z, last reached configuration (see `loop1_decider0`) and tape head position
    - h1: ListES*Z, one-before-last reached configuration and tape head position
    - ls: list (ListES*Z), history of visited configurations and tape head positions

  Returns true iff a loop (including translated loopss) is detected in the history of configurations.
*)
Definition find_loop1_0(h0 h1:ListES*Z)(ls:list (ListES*Z)):bool :=
match ls with
| h2::ls' => find_loop1 h0 h1 h2 (h1::ls) ls ls' O
| nil => false
end.

(** Loop decider function: runs `n` steps of the Turing machine and stores the history
of seen configurations (`ListES`) and tape head positions. After `n` steps, the function calls
`find_loop1_0` to try and detect a potential loop.

  Args:
    - tm: TM Σ, the Turing machine that the loop decider is checking.
    - n: nat, gas parameter
    - es:ListES, current configuration (ExecState), using the `ListES` representation, see List_Tape.v
    - d: Z, current head position index on the tape
    - ls: list (ListES*Z), list of visited configurations and head positions

  Returns:
    - HaltDecideResult:
      - Result_Halt s i: the Turing machine halts at configuration (s,i)
      - Result_NonHalt: the Turing machine does not halt
      - Result_Unknown: the decider cannot conclude
*)
Fixpoint loop1_decider0(tm:TM Σ)(n:nat)(es:ListES)(d:Z)(ls:list (ListES*Z)):HaltDecideResult :=
match n with
| O => Result_Unknown
| S n0 =>
  match tm es.(s) es.(m) with
  | None => Result_Halt es.(s) es.(m)
  | Some tr =>
    let es' := ListES_step' tr es in
    let d' := (d+Dir_to_Z tr.(dir _))%Z in
    let ls' := ((es,d)::ls) in
    match n0 with
    | S n0' =>
      loop1_decider0 tm n0 es' d' ls'
    | O =>
      if find_loop1_0 (es',d') (es,d) ls then Result_NonHalt else
      loop1_decider0 tm n0 es' d' ls'
    end
  end
end.

(** Loop decider entrypoint function.

  Args:
    - n: nat, gas parameter
    - tm: TM Σ, the Turing machine that the loop decider is checking.

  Returns:
    - HaltDecideResult:
      - Result_Halt s i: the Turing machine halts at configuration (s,i)
      - Result_NonHalt: the Turing machine does not halt
      - Result_Unknown: the decider cannot conclude
*)
Definition loop1_decider(n:nat)(tm:TM Σ):HaltDecideResult :=
  loop1_decider0 tm n {| l:=nil; r:=nil; m:=Σ0; s:=St0 |} Z0 nil.

(* End: Loop decider implementation *)

(* Begin: Proofs *)

Lemma verify_loop1_spec tm h1 h2 ls1 ls2 n d:
  (exists h0 ls0 n0 n1,
  sidpos_history_WF tm h0 ls0 /\
  (h1::ls1) = skipn n0 (h0::ls0) /\
  (h2::ls2) = skipn (S n1) (h1::ls1) /\
  sidpos_history_period h0 ls0 n0 (S n1) /\
  n0+n=(S n1)) ->
  verify_loop1 h1 h2 ls1 ls2 n d = true ->
  ~ HaltsFromInit Σ Σ0 tm.
Proof.
  gd ls2. gd h2. gd h1. gd n.
  induction ls1; intros.
  - cbn in H0.
    destruct h1,h2.
    repeat rewrite andb_shortcut_spec in H0.
    repeat rewrite Bool.andb_true_iff in H0.
    repeat rewrite orb_shortcut_spec in H0.
    repeat rewrite Bool.orb_true_iff in H0.
    destruct H0 as [H0a [H0b [H0c _]]].
    destruct H as [h0 [ls0 [N [T [Ha [Hb [Hc [Hd He]]]]]]]].
    destruct n; cg.
    cbn in Hc. rewrite skipn_nil in Hc. invst Hc.
  - cbn in H0.
    destruct h1,h2.
    repeat rewrite andb_shortcut_spec in H0.
    repeat rewrite Bool.andb_true_iff in H0.
    repeat rewrite orb_shortcut_spec in H0.
    repeat rewrite Bool.orb_true_iff in H0.
    destruct H0 as [H0a [H0b H0c]].

    destruct H as [h0 [ls0 [N [T [Ha [Hb [Hc [Hd He]]]]]]]].
    St_eq_dec (s l) (s l0); cg.
    Σ_eq_dec (m l) (m l0); cg.
    clrs.

    destruct ls2 as [|h2' ls2']; cg.
    + destruct H0c as [H0c|H0c]; cg.
      destruct n; cg.
      epose proof (sidpos_history_period_S Hb Hc Hd H H0).
      assert (N=S T) by lia; subst.
      eapply loop1_nonhalt'; eauto 1.
    + destruct H0c as [H0c|H0c].
      * destruct n; cg.
        epose proof (sidpos_history_period_S Hb Hc Hd H H0).
        assert (N=S T) by lia; subst.
        eapply loop1_nonhalt'; eauto 1.
      * destruct n; cbn in H0c.
        {
          eapply IHls1; eauto 1.
          destruct ls0 as [|h0' ls0'].
          1: destruct N; [lia | cbn in Hb; rewrite skipn_nil in Hb; invst Hb].
          exists h0'. exists ls0'. exists N. exists T.
          repeat split; auto 1; try lia.
          2,3: eapply skipn_S'; eauto 1.
          1: eapply sidpos_history_WF_cdr,Ha.
          destruct N as [|N]. 1: lia.
          epose proof (sidpos_history_period_S' Hd) as Hd'. clear Hd.
          cbn in Hb.
          eapply sidpos_history_period_S; eauto 1.
        }
        {
          eapply IHls1; eauto 1.
          exists h0. exists ls0. exists (S N). exists T.
          repeat split; auto 1; try lia.
          1,2: eapply skipn_S; eauto 1.
          apply (sidpos_history_period_S Hb Hc Hd H H0).
        }
Qed.



Lemma find_loop1_spec tm h0 h1 h2 ls0 ls1 ls2 n:
  sidpos_history_WF tm h0 ls0 ->
  h1::ls1 = skipn (S n) (h0::ls0) ->
  h2::ls2 = skipn (S n) (h1::ls1) ->
  find_loop1 h0 h1 h2 ls0 ls1 ls2 n = true ->
  ~ HaltsFromInit Σ Σ0 tm.
Proof.
  gd n. gd ls2. gd h2. gd h1.
  induction ls1.
  - intros. cbn in H2.
    cbn in H1. rewrite skipn_nil in H1.
    invst H1.
  - intros. cbn in H2.
    repeat rewrite orb_shortcut_spec in H2.
    rewrite Bool.orb_true_iff in H2.
    destruct H2 as [H2|H2].
    + destruct h0 as [es0 d0].
      destruct h1 as [es1 d1].
      destruct h2 as [es2 d2].
      repeat rewrite andb_shortcut_spec in H2.
      repeat rewrite Bool.andb_true_iff in H2.
      destruct H2 as [H2a [H2b [H2c [H2d H2e]]]].
      eapply verify_loop1_spec; eauto 1.
      eexists. eexists. exists 0. eexists.
      repeat split; auto 1.
      unfold sidpos_history_period. intros. lia.
    + destruct ls2 as [|h3 [|h2' ls2']]; cg.
      eapply IHls1; eauto 1.
      * rewrite (skipn_S H0); cg.
      * cbn in H1.
        apply (skipn_S (skipn_S H1)).
Qed.


Lemma find_loop1_0_spec tm h0 h1 ls:
  sidpos_history_WF tm h0 (h1::ls) ->
  find_loop1_0 h0 h1 ls = true ->
  ~HaltsFromInit Σ Σ0 tm.
Proof.
  intros.
  unfold find_loop1_0 in H0.
  destruct ls; cg.
  eapply find_loop1_spec; eauto 1; reflexivity.
Qed.

Lemma loop1_decider0_def(tm:TM Σ)(n:nat)(es:ListES)(d:Z)(ls:list (ListES*Z)):
loop1_decider0 tm n es d ls =
match n with
| O => Result_Unknown
| S n0 =>
  match tm es.(s) es.(m) with
  | None => Result_Halt es.(s) es.(m)
  | Some tr =>
    let es' := ListES_step' tr es in
    let d' := (d+Dir_to_Z tr.(dir _))%Z in
    let ls' := ((es,d)::ls) in
    match n0 with
    | S n0' =>
      loop1_decider0 tm n0 es' d' ls' 
    | O =>
      if find_loop1_0 (es',d') (es,d) ls then Result_NonHalt else
      loop1_decider0 tm n0 es' d' ls'
    end
  end
end.
Proof.
  unfold loop1_decider0.
  destruct n; cbn; reflexivity.
Qed.

Lemma loop1_decider0_spec tm n es d ls:
  sidpos_history_WF tm (es,d) ls ->
  match loop1_decider0 tm n es d ls with
  | Result_Halt s0 i0 =>
    exists n1 es0,
    n1<n+(List.length ls) /\
    HaltsAt Σ tm n1 (InitES Σ Σ0) /\
    Steps Σ tm n1 (InitES Σ Σ0) (ListES_toES es0) /\
    es0.(s)=s0 /\ es0.(m)=i0
  | Result_NonHalt => ~HaltsFromInit Σ Σ0 tm
  | Result_Unknown => True
  end.
Proof.
  gd ls. gd d. gd es.
  induction n; intros.
  1: cbn; trivial.
  destruct es as [l0 r0 m0 s0] eqn:Ees.
  rewrite loop1_decider0_def.
  rewrite s_def,m_def.
  destruct (tm s0 m0) eqn:E.
  - rewrite <-Ees.
    destruct t as [s1 d1 o1].
    epose proof (sidpos_history_WF_S H E) as H0.
    rewrite <-Ees in H0.
    remember {| nxt := s1; dir := d1; out := o1 |} as t.
    remember (ListES_step' t es) as es'.
    remember (d + Dir_to_Z (dir Σ t))%Z as d'.
    remember ((es, d) :: ls) as ls'.
    destruct n.
    + cbn.
      destruct (find_loop1_0 (es', d') (es, d) ls) eqn:E1.
      2: trivial.
      eapply find_loop1_0_spec; eauto 1.
      rewrite Heqt in Heqd'. cbn in Heqd'. subst d'. subst ls'. apply H0.
    + replace (let es'0 := es' in
      let d'0 := d' in let ls'0 := ls' in loop1_decider0 tm (S n) es'0 d'0 ls'0) with
      (loop1_decider0 tm (S n) es' d' ls') by reflexivity.
      specialize (IHn _ _ _ H0).
      rewrite Heqt in Heqd'. cbn in Heqd'. subst d'. subst ls'.
      replace (S n + List.length ((es, d) :: ls)) with (S (S n) + List.length ls) in IHn by (cbn; lia).
      apply IHn.
  - exists (List.length ls). exists es.
    repeat split.
    + lia.
    + eexists.
      split.
      1: apply (MoveDist_Steps (sidpos_history_hd H)).
      unfold step,ListES_toES. rewrite E. reflexivity.
    + subst es. apply (MoveDist_Steps (sidpos_history_hd H)).
    + subst es.  reflexivity.
    + subst es.  reflexivity.
Qed.

Lemma loop1_decider_WF BB n:
  n<=S BB ->
  HaltDecider_WF BB (loop1_decider n).
Proof.
  intros.
  unfold HaltDecider_WF,loop1_decider.
  intro tm.
  eassert (H0:_). {
    apply (loop1_decider0_spec tm n {| l := nil; r := nil; m := Σ0; s := St0 |} 0 nil).
    apply sidpos_history_WF_O.
  }
  destruct (loop1_decider0 tm n {| l := nil; r := nil; m := Σ0; s := St0 |} 0 nil); auto 1.
  cbn in H0.
  destruct H0 as [n1 [es0 [H0 [H1 [H2 [H3 H4]]]]]].
  destruct (ListES_toES es0) as [s1 t0] eqn:E0.
  exists n1. exists t0.
  destruct es0 eqn:E.
  cbn in E0.
  inversion E0. subst s1.
  repeat split; auto 1.
  2: lia. rewrite <-E0 in H2.
  cbn in H3,H4. subst.
  apply H2.
Qed.

(* End: Proofs *)