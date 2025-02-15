Require Import List.

From CoqBB5 Require Import TM.
From CoqBB5 Require Import BB5_Decider_Pipeline.

Definition tm_Lp1 :=
(makeTM BR1 HR1 CL1 EL0 DR1 BL0 DR0 AR1 CL0 AR0,Lp1)::
(makeTM BR1 ER0 CL1 AR0 CL0 DL1 AL1 HR1 BR0 DL0,Lp1)::
nil.