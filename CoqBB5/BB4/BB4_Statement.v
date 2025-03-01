(** 
  This files contains the theorem statement of "BB(4) = 107" as well as the definitions needed for the statement.
  The statement (see `BB4_value_statement`) and the definitions are quite transparent, the only prerequisite is to know what Turing machine are.
*)

Require Import ZArith.

(** 4-state Turing machines *)
Inductive St:Set :=
| St0
| St1
| St2
| St3.

(** 2-symbol Turing machines *)
Inductive Σ:Set :=
| Σ0
| Σ1.

(** Equality on states *)
Definition St_eqb(s1 s2:St) :=
match s1,s2 with
| St0,St0 | St1,St1 | St2,St2 | St3,St3 => true
| _,_ => false
end.

(** Equality on alphabet symbols *)
Definition Σ_eqb(i1 i2:Σ) :=
match i1,i2 with
| Σ0,Σ0 | Σ1,Σ1 => true
| _,_ => false
end.

(** Left/Right move direction *)
Inductive Dir:Set :=
| Dneg
| Dpos.

(** Mapping Left to -1 and Right to 1 *)
Definition Dir_to_Z(x:Dir) :=
match x with
| Dneg => Zneg 1
| Dpos => Zpos 1
end.

Section TM.

(** Σ is the Turing machine's alphabet and Σ0 the zero symbol *)
Hypothesis Σ:Set.
Hypothesis Σ0:Σ.

(** Turing machine transition: `nxt` next state, `dir` head move direction, `out` written symbol *)
Record Trans:Set := {
  nxt: St;
  dir: Dir;
  out: Σ;
}.

(** Turing machine partial transition function: the function returns the transition for a given state and read symbol.
Undefined transitions are encoded with None. *)
Definition TM:Set := St->Σ->option Trans.

(** Turing machine Execution State (ES), also known as "configuration" encodes the current state and tape content.
The tape content is represented as a function from integers to symbols, where 0 corresponds to the current head position.
*)
Definition ExecState:Set := St*(Z->Σ).

(** Initial configuration: state 0 and all-0 tape *)
Definition InitES:ExecState := (St0,fun _=>Σ0).

(** Tape content update *)
Definition upd(t:(Z->Σ))(o:Σ) :=
  fun x:Z => if Z.eqb x Z0 then o else t x.

(** Head position update, implemented by translating the tape content function *)
Definition mov(t:(Z->Σ))(d:Dir) :=
  fun x:Z => t ((x+(Dir_to_Z d))%Z).

(** Turing machine step: returns the next configuration or None if the machine has halted *)
Definition step(tm:TM)(st:ExecState): option ExecState :=
  let (s,t):=st in
  let read_symbol := t Z0 in
  match tm s read_symbol with
  | None => None
  | Some tr =>
    let (s',d,o):=tr in
    Some (s',mov (upd t o) d)
  end.

(** `Steps tm n st1 st2` holds if configuration `st2` is reached from `st1` after `n` Turing machine steps. *)
Inductive Steps: TM->nat->ExecState->ExecState->Prop :=
| steps_O tm st:
  Steps tm O st st
| steps_S tm n st st0 st1:
  Steps tm n st st0 ->
  step tm st0 = Some st1 ->
  Steps tm (S n) st st1.

(** `HaltsAtPlusOne tm n st` holds if Turing machine `tm` halts at configuration `st` after `n` steps.

  Note: Coq-BB5 'HaltsAt' definition (see TM.v) is off by one compared to Radò's definition which is why we have to use 'HaltsAtPlusOne'
        here in order to prove BB(5) = 47176870 and not BB(5) = 47176869.
*)
Inductive HaltsAtPlusOne(tm:TM): nat->ExecState->Prop :=
| HaltsAtPlusOne_intro n st:
  (exists st', Steps tm n st st' /\ step tm st' = None) ->
  HaltsAtPlusOne tm (S n) st.

End TM.

Definition BB4 := 107%N.

(** Main theorem statement: BB(4) = 107. The statement is split into two parts:
  
  - Upper bound (hard): For all 4-state 2-symbol Turing machine `tm` and natural number `n0`, if `tm` halts at `n0` steps, then `n0` is less than or equal to 107.
  - Lower bound (easy): There exists a Turing machine `tm` that halts at 107 steps.
*)
Definition BB4_value_statement :=
  (forall tm n0, HaltsAtPlusOne Σ tm n0 (InitES Σ Σ0) -> n0 <= N.to_nat BB4) /\
  (exists tm, HaltsAtPlusOne Σ tm (N.to_nat BB4) (InitES Σ Σ0)).