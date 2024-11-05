Require Import List.

From BusyCoq Require Import BB52Statement.
From BusyCoq Require Import TM_CoqBB5.
From BusyCoq Require Import Decider_Pipeline.

Definition DFA_from_list(ls:list(nat*nat))(x:nat)(i:Σ) :=
  let (a,b) := nth x ls (0,0) in
  match i with
  | Σ0 => a
  | Σ1 => b
  end.

Definition tm_DNV :=
(makeTM BR1 AR0 CL1 HR1 DL0 CL0 ER0 AR1 ER1 DL1,
DNV 2 (DFA_from_list ((0,1)::(2,0)::(2,2)::nil)))::

(makeTM BR1 CL1 AL1 BR1 DL1 AL0 ER1 DR0 HR1 BR0,
DNV 12 (DFA_from_list ((0,1)::(2,3)::(4,5)::(4,6)::(4,4)::(4,7)::(4,8)::(4,9)::(4,10)::(4,11)::(4,3)::(4,12)::(4,7)::nil)))::

(makeTM BR1 AL1 AL1 CR1 HR1 DR0 AL0 ER0 DL0 ER1,
DNV 3 (DFA_from_list ((0,1)::(2,3)::(2,2)::(0,1)::nil)))::

(makeTM BR1 HR1 CR0 BR0 CL1 DL0 AR1 EL0 AL0 EL0,
DNV 10 (DFA_from_list ((0,1)::(2,3)::(4,4)::(5,6)::(4,4)::(7,4)::(8,4)::(9,10)::(4,4)::(5,6)::(4,3)::nil)))::

(makeTM BR1 AR1 CL1 DL0 HR1 DL1 ER1 EL1 AR0 BL0,
DNV 9 (DFA_from_list ((0,1)::(2,3)::(4,5)::(6,0)::(4,4)::(4,7)::(4,8)::(4,2)::(4,9)::(4,6)::nil)))::

(makeTM BR1 BL1 CR0 DL0 DR1 CR1 EL1 AL0 HR1 AL1,
DNV 9 (DFA_from_list ((0,1)::(2,3)::(4,5)::(6,0)::(4,4)::(4,7)::(4,8)::(4,2)::(4,9)::(4,6)::nil)))::

(makeTM BR1 AL1 CR1 DR1 AL0 ER0 HR1 CR0 CL0 ER1,
DNV 3 (DFA_from_list ((0,1)::(2,3)::(2,2)::(0,1)::nil)))::

(makeTM BR1 AR1 CL1 CL0 EL0 DR0 AR0 BL1 DL1 HR1,
DNV 10 (DFA_from_list ((0,1)::(2,3)::(4,5)::(5,5)::(6,7)::(5,5)::(5,5)::(8,9)::(5,5)::(10,4)::(4,5)::nil)))::

(makeTM BR1 HR1 CR0 BR0 DL0 AL1 DL1 EL1 AL0 EL0,
DNV 3 (DFA_from_list ((0,1)::(2,1)::(1,3)::(3,3)::nil)))::

(makeTM BR1 DR0 CR1 HR1 DL1 EL1 ER1 DL1 AR1 CL0,
DNV 10 (DFA_from_list ((0,1)::(2,3)::(4,5)::(2,3)::(6,7)::(8,8)::(9,6)::(9,6)::(4,10)::(9,9)::(8,8)::nil)))::

(makeTM BR1 AR0 CL1 HR1 DL0 CL0 ER0 AR1 ER1 AR0,
DNV 2 (DFA_from_list ((0,1)::(2,0)::(2,2)::nil)))::

(makeTM BR1 HR1 CL0 DR1 DL1 CL1 ER1 ER0 AR0 BL0,
DNV 11 (DFA_from_list ((0,1)::(2,3)::(4,5)::(2,3)::(6,7)::(6,8)::(6,6)::(6,8)::(9,10)::(4,6)::(11,7)::(6,5)::nil)))::

(makeTM BR1 BR0 CR0 DL0 DR1 HR1 EL0 AR1 AL1 EL1,
DNV 10 (DFA_from_list ((0,1)::(2,1)::(3,4)::(5,6)::(5,7)::(5,5)::(5,7)::(8,9)::(3,5)::(10,6)::(5,4)::nil)))::

(makeTM BR1 HR1 CR0 BR0 DL0 EL1 DL1 EL0 AL1 CR1,
DNV 3 (DFA_from_list ((0,1)::(2,1)::(1,3)::(3,3)::nil)))::

(makeTM BR1 CR1 CL1 BR1 DL1 AR0 EL1 BL0 AL1 HR1,
DNV 8 (DFA_from_list ((0,1)::(2,1)::(3,4)::(5,6)::(7,2)::(5,5)::(5,5)::(3,8)::(7,2)::nil)))::

(makeTM BR1 DL1 CL1 HR1 DL0 CL0 ER0 AR1 ER1 AR0,
DNV 2 (DFA_from_list ((0,1)::(2,0)::(2,2)::nil)))::

(makeTM BR1 AL1 CR1 EL0 DR1 AR0 ER1 HR1 AL1 BL1,
DNV 10 (DFA_from_list ((0,1)::(2,3)::(4,5)::(2,3)::(4,4)::(4,6)::(7,8)::(4,9)::(6,6)::(4,10)::(4,10)::nil)))::

(makeTM BR1 HR1 CR0 BR0 DL0 EL1 DL1 EL0 AL1 EL0,
DNV 3 (DFA_from_list ((0,1)::(2,1)::(1,3)::(3,3)::nil)))::

(makeTM BR1 EL0 CR1 HR1 DR0 CR0 DL1 AL0 BL0 EL0,
DNV 9 (DFA_from_list ((0,1)::(2,3)::(4,4)::(5,6)::(4,4)::(7,4)::(2,4)::(8,9)::(5,6)::(4,3)::nil)))::

(makeTM BR1 AR0 CL1 HR1 CL0 DL0 ER1 BR0 ER0 AR1,
DNV 3 (DFA_from_list ((0,1)::(2,3)::(1,0)::(3,3)::nil)))::

(makeTM BR1 HR1 CL1 DL1 DR1 CL1 ER1 BL0 AR1 CR0,
DNV 10 (DFA_from_list ((0,1)::(2,3)::(4,5)::(2,3)::(6,4)::(6,7)::(6,6)::(8,9)::(6,10)::(7,7)::(6,4)::nil)))::

(makeTM BR1 HR1 CR0 BR0 DL0 EL1 DL1 CR1 AL1 EL0,
DNV 3 (DFA_from_list ((0,1)::(2,1)::(1,3)::(3,3)::nil)))::

(makeTM BR1 DL0 CR1 ER0 DR1 HR1 EL1 AL1 AR1 EL1,
DNV 10 (DFA_from_list ((0,1)::(2,3)::(4,5)::(2,3)::(4,4)::(4,6)::(7,8)::(4,9)::(6,6)::(4,10)::(4,10)::nil)))::

nil.