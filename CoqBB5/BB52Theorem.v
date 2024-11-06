Require Import List.
Require Import ZArith.
Require Import Logic.FunctionalExtensionality.
Require Import Lia.
Require Import FSets.FMapPositive.

From CoqBB5 Require Import BB52Statement.
From CoqBB5 Require Import TNF.
From CoqBB5 Require Import ListTape.
From CoqBB5 Require Import TM.
From CoqBB5 Require Import Prelims.
From CoqBB5 Require Import Encodings.
From CoqBB5 Require Import CustomTactics.
From CoqBB5 Require Import Decider_Pipeline.


From CoqBB5 Require Import Deciders.Decider_Loop.
From CoqBB5 Require Import Deciders.Decider_NGramCPS.


From CoqBB5 Require Import Deciders_CustomParameters.Decider_Loop_CustomParameters.
From CoqBB5 Require Import Deciders_CustomParameters.Decider_NGramCPS_CustomParameters.
From CoqBB5 Require Import Deciders_CustomParameters.Decider_Verifier_FAR_CustomParameters.
From CoqBB5 Require Import Deciders_CustomParameters.Decider_Verifier_FAR_MITM_WDFA_CustomParameters.
From CoqBB5 Require Import Deciders_CustomParameters.Decider_RepWL_CustomParameters.
From CoqBB5 Require Import Deciders_CustomParameters.Decider_Halt_CustomParameters.



From CoqBB5 Require Import Sporadic_NonHalt.


Definition check_tms(ls:list ((TM Σ)*DeciderType)):=
  map (fun (x:(TM Σ)*DeciderType)=> let (tm,d):=x in getDecider d tm) ls.

(*
Compute (length tm_WA).
Time Definition check_res := Eval vm_compute in (check_tms ((tm_WA))).
Compute (filter (fun x => match x with Result_NonHalt => false | _ => true end) check_res).
Compute check_res.
*)


Definition tm_list :=
  tm_RWL::
  tm_NG0::tm_NG2::tm_NG3::tm_NG4::tm_NG5::tm_NG6::tm_NG7::tm_NG_ge8::
  tm_Ha::
  tm_Lp1::
  tm_NG_LRU::
  tm_NG0'::tm_RWL'::
  tm_DNV::tm_WA::
  (map (fun tm => (tm,Holdout)) tm_holdouts_13)::
  nil.


Definition TM_enc(tm:TM Σ):positive :=
  match TM_to_N tm with
  | N0 => xH
  | Npos v => Pos.succ v
  end.

Fixpoint TM_ins_all(ls:list ((TM Σ)*DeciderType))(mp:PositiveMap.tree DeciderType):PositiveMap.tree DeciderType :=
match ls with
| nil => mp
| (h1,h2)::t => TM_ins_all t (PositiveMap.add (TM_enc h1) h2 mp)
end.

Fixpoint TM_ins_all'(ls:list (list ((TM Σ)*DeciderType)))(mp:PositiveMap.tree DeciderType):PositiveMap.tree DeciderType :=
match ls with
| nil => mp
| h::t => TM_ins_all' t (TM_ins_all h mp)
end.

Time Definition tm_decider_table :=
  Eval vm_compute in (TM_ins_all' tm_list (PositiveMap.empty DeciderType)).

Definition table_based_decider(tm:TM Σ):HaltDecideResult :=
  match PositiveMap.find (TM_enc tm) tm_decider_table with
  | None => Result_Unknown
  | Some d => getDecider d tm
  end.

Lemma table_based_decider_spec: HaltDecider_WF (N.to_nat BB5_minus_one) table_based_decider.
Proof.
  unfold HaltDecider_WF,table_based_decider.
  intros tm.
  destruct (PositiveMap.find (TM_enc tm) tm_decider_table).
  2: trivial.
  apply getDecider_spec.
Qed.

Definition NF_decider(dec:HaltDecider)(tm:TM Σ):HaltDecideResult :=
  match dec (TM_to_NF tm) with
  | Result_NonHalt => Result_NonHalt
  | _ => Result_Unknown
  end.

Lemma NF_decider_spec dec n:
  HaltDecider_WF n dec ->
  HaltDecider_WF n (NF_decider dec).
Proof.
  unfold HaltDecider_WF,NF_decider.
  intro H.
  intro tm.
  specialize (H (TM_to_NF tm)).
  destruct (dec (TM_to_NF tm)).
  1,3: trivial.
  unfold HaltsFromInit.
  unfold HaltsFromInit in H.
  rewrite <-NonHalt_iff.
  rewrite <-NonHalt_iff in H.
  rewrite <-TM_to_NF_spec in H.
  apply H.
Qed.

Definition decider_all :=
  (HaltDecider_list
(decider2::decider3::decider4::decider5::decider6::decider7::decider8::
decider9::decider10::
decider11::decider12::
decider13::decider14::
table_based_decider::
(NF_decider table_based_decider)::
nil)).

Lemma decider_all_spec: HaltDecider_WF (N.to_nat BB5_minus_one) decider_all.
Proof.
  unfold decider_all,HaltDecider_list.
  repeat apply HaltDecider_cons_spec.
  all: try apply NGramCPS_decider_impl2_spec.
  all: try apply NGramCPS_decider_impl1_spec.
  - apply decider2_WF.
  - apply loop1_decider_WF.
    unfold BB5_minus_one. lia.
  - apply table_based_decider_spec.
  - apply NF_decider_spec,table_based_decider_spec.
  - unfold HaltDecider_nil,HaltDecider_WF.
    intro. trivial.
Qed.

Definition q0 := root_q_upd1_simplified.

Definition q_suc:SearchQueue->SearchQueue := (fun x => SearchQueue_upds x decider_all 20).

Definition q_0 := q0.

Definition q_1_def := q_suc q_0.
Time Definition q_1 := Eval native_compute in q_1_def.
Definition q_2_def := q_suc q_1.
Time Definition q_2 := Eval native_compute in q_2_def.
Definition q_3_def := q_suc q_2.
Time Definition q_3 := Eval native_compute in q_3_def.
Definition q_4_def := q_suc q_3.
Time Definition q_4 := Eval native_compute in q_4_def.
Definition q_5_def := q_suc q_4.
Time Definition q_5 := Eval native_compute in q_5_def.
Definition q_6_def := q_suc q_5.
Time Definition q_6 := Eval native_compute in q_6_def.
Definition q_7_def := q_suc q_6.
Time Definition q_7 := Eval native_compute in q_7_def.
Definition q_8_def := q_suc q_7.
Time Definition q_8 := Eval native_compute in q_8_def.
Definition q_9_def := q_suc q_8.
Time Definition q_9 := Eval native_compute in q_9_def.
Definition q_10_def := q_suc q_9.
Time Definition q_10 := Eval native_compute in q_10_def.
Definition q_11_def := q_suc q_10.
Time Definition q_11 := Eval native_compute in q_11_def.
Definition q_12_def := q_suc q_11.
Time Definition q_12 := Eval native_compute in q_12_def.
Definition q_13_def := q_suc q_12.
Time Definition q_13 := Eval native_compute in q_13_def.
Definition q_14_def := q_suc q_13.
Time Definition q_14 := Eval native_compute in q_14_def.
Definition q_15_def := q_suc q_14.
Time Definition q_15 := Eval native_compute in q_15_def.
Definition q_16_def := q_suc q_15.
Time Definition q_16 := Eval native_compute in q_16_def.
Definition q_17_def := q_suc q_16.
Time Definition q_17 := Eval native_compute in q_17_def.
Definition q_18_def := q_suc q_17.
Time Definition q_18 := Eval native_compute in q_18_def.
Definition q_19_def := q_suc q_18.
Time Definition q_19 := Eval native_compute in q_19_def.
Definition q_20_def := q_suc q_19.
Time Definition q_20 := Eval native_compute in q_20_def.
Definition q_21_def := q_suc q_20.
Time Definition q_21 := Eval native_compute in q_21_def.
Definition q_22_def := q_suc q_21.
Time Definition q_22 := Eval native_compute in q_22_def.
Definition q_23_def := q_suc q_22.
Time Definition q_23 := Eval native_compute in q_23_def.
Definition q_24_def := q_suc q_23.
Time Definition q_24 := Eval native_compute in q_24_def.
Definition q_25_def := q_suc q_24.
Time Definition q_25 := Eval native_compute in q_25_def.
Definition q_26_def := q_suc q_25.
Time Definition q_26 := Eval native_compute in q_26_def.
Definition q_27_def := q_suc q_26.
Time Definition q_27 := Eval native_compute in q_27_def.
Definition q_28_def := q_suc q_27.
Time Definition q_28 := Eval native_compute in q_28_def.
Definition q_29_def := q_suc q_28.
Time Definition q_29 := Eval native_compute in q_29_def.
Definition q_30_def := q_suc q_29.
Time Definition q_30 := Eval native_compute in q_30_def.
Definition q_31_def := q_suc q_30.
Time Definition q_31 := Eval native_compute in q_31_def.
Definition q_32_def := q_suc q_31.
Time Definition q_32 := Eval native_compute in q_32_def.
Definition q_33_def := q_suc q_32.
Time Definition q_33 := Eval native_compute in q_33_def.
Definition q_34_def := q_suc q_33.
Time Definition q_34 := Eval native_compute in q_34_def.
Definition q_35_def := q_suc q_34.
Time Definition q_35 := Eval native_compute in q_35_def.
Definition q_36_def := q_suc q_35.
Time Definition q_36 := Eval native_compute in q_36_def.
Definition q_37_def := q_suc q_36.
Time Definition q_37 := Eval native_compute in q_37_def.
Definition q_38_def := q_suc q_37.
Time Definition q_38 := Eval native_compute in q_38_def.
Definition q_39_def := q_suc q_38.
Time Definition q_39 := Eval native_compute in q_39_def.
Definition q_40_def := q_suc q_39.
Time Definition q_40 := Eval native_compute in q_40_def.
Definition q_41_def := q_suc q_40.
Time Definition q_41 := Eval native_compute in q_41_def.
Definition q_42_def := q_suc q_41.
Time Definition q_42 := Eval native_compute in q_42_def.
Definition q_43_def := q_suc q_42.
Time Definition q_43 := Eval native_compute in q_43_def.
Definition q_44_def := q_suc q_43.
Time Definition q_44 := Eval native_compute in q_44_def.
Definition q_45_def := q_suc q_44.
Time Definition q_45 := Eval native_compute in q_45_def.
Definition q_46_def := q_suc q_45.
Time Definition q_46 := Eval native_compute in q_46_def.
Definition q_47_def := q_suc q_46.
Time Definition q_47 := Eval native_compute in q_47_def.
Definition q_48_def := q_suc q_47.
Time Definition q_48 := Eval native_compute in q_48_def.
Definition q_49_def := q_suc q_48.
Time Definition q_49 := Eval native_compute in q_49_def.
Definition q_50_def := q_suc q_49.
Time Definition q_50 := Eval native_compute in q_50_def.
Definition q_51_def := q_suc q_50.
Time Definition q_51 := Eval native_compute in q_51_def.
Definition q_52_def := q_suc q_51.
Time Definition q_52 := Eval native_compute in q_52_def.
Definition q_53_def := q_suc q_52.
Time Definition q_53 := Eval native_compute in q_53_def.
Definition q_54_def := q_suc q_53.
Time Definition q_54 := Eval native_compute in q_54_def.
Definition q_55_def := q_suc q_54.
Time Definition q_55 := Eval native_compute in q_55_def.
Definition q_56_def := q_suc q_55.
Time Definition q_56 := Eval native_compute in q_56_def.
Definition q_57_def := q_suc q_56.
Time Definition q_57 := Eval native_compute in q_57_def.
Definition q_58_def := q_suc q_57.
Time Definition q_58 := Eval native_compute in q_58_def.
Definition q_59_def := q_suc q_58.
Time Definition q_59 := Eval native_compute in q_59_def.
Definition q_60_def := q_suc q_59.
Time Definition q_60 := Eval native_compute in q_60_def.
Definition q_61_def := q_suc q_60.
Time Definition q_61 := Eval native_compute in q_61_def.
Definition q_62_def := q_suc q_61.
Time Definition q_62 := Eval native_compute in q_62_def.
Definition q_63_def := q_suc q_62.
Time Definition q_63 := Eval native_compute in q_63_def.
Definition q_64_def := q_suc q_63.
Time Definition q_64 := Eval native_compute in q_64_def.
Definition q_65_def := q_suc q_64.
Time Definition q_65 := Eval native_compute in q_65_def.
Definition q_66_def := q_suc q_65.
Time Definition q_66 := Eval native_compute in q_66_def.
Definition q_67_def := q_suc q_66.
Time Definition q_67 := Eval native_compute in q_67_def.
Definition q_68_def := q_suc q_67.
Time Definition q_68 := Eval native_compute in q_68_def.
Definition q_69_def := q_suc q_68.
Time Definition q_69 := Eval native_compute in q_69_def.
Definition q_70_def := q_suc q_69.
Time Definition q_70 := Eval native_compute in q_70_def.
Definition q_71_def := q_suc q_70.
Time Definition q_71 := Eval native_compute in q_71_def.
Definition q_72_def := q_suc q_71.
Time Definition q_72 := Eval native_compute in q_72_def.
Definition q_73_def := q_suc q_72.
Time Definition q_73 := Eval native_compute in q_73_def.
Definition q_74_def := q_suc q_73.
Time Definition q_74 := Eval native_compute in q_74_def.
Definition q_75_def := q_suc q_74.
Time Definition q_75 := Eval native_compute in q_75_def.
Definition q_76_def := q_suc q_75.
Time Definition q_76 := Eval native_compute in q_76_def.
Definition q_77_def := q_suc q_76.
Time Definition q_77 := Eval native_compute in q_77_def.
Definition q_78_def := q_suc q_77.
Time Definition q_78 := Eval native_compute in q_78_def.
Definition q_79_def := q_suc q_78.
Time Definition q_79 := Eval native_compute in q_79_def.
Definition q_80_def := q_suc q_79.
Time Definition q_80 := Eval native_compute in q_80_def.
Definition q_81_def := q_suc q_80.
Time Definition q_81 := Eval native_compute in q_81_def.
Definition q_82_def := q_suc q_81.
Time Definition q_82 := Eval native_compute in q_82_def.
Definition q_83_def := q_suc q_82.
Time Definition q_83 := Eval native_compute in q_83_def.
Definition q_84_def := q_suc q_83.
Time Definition q_84 := Eval native_compute in q_84_def.
Definition q_85_def := q_suc q_84.
Time Definition q_85 := Eval native_compute in q_85_def.
Definition q_86_def := q_suc q_85.
Time Definition q_86 := Eval native_compute in q_86_def.
Definition q_87_def := q_suc q_86.
Time Definition q_87 := Eval native_compute in q_87_def.
Definition q_88_def := q_suc q_87.
Time Definition q_88 := Eval native_compute in q_88_def.
Definition q_89_def := q_suc q_88.
Time Definition q_89 := Eval native_compute in q_89_def.
Definition q_90_def := q_suc q_89.
Time Definition q_90 := Eval native_compute in q_90_def.
Definition q_91_def := q_suc q_90.
Time Definition q_91 := Eval native_compute in q_91_def.
Definition q_92_def := q_suc q_91.
Time Definition q_92 := Eval native_compute in q_92_def.
Definition q_93_def := q_suc q_92.
Time Definition q_93 := Eval native_compute in q_93_def.
Definition q_94_def := q_suc q_93.
Time Definition q_94 := Eval native_compute in q_94_def.
Definition q_95_def := q_suc q_94.
Time Definition q_95 := Eval native_compute in q_95_def.
Definition q_96_def := q_suc q_95.
Time Definition q_96 := Eval native_compute in q_96_def.
Definition q_97_def := q_suc q_96.
Time Definition q_97 := Eval native_compute in q_97_def.
Definition q_98_def := q_suc q_97.
Time Definition q_98 := Eval native_compute in q_98_def.
Definition q_99_def := q_suc q_98.
Time Definition q_99 := Eval native_compute in q_99_def.
Definition q_100_def := q_suc q_99.
Time Definition q_100 := Eval native_compute in q_100_def.
Definition q_101_def := q_suc q_100.
Time Definition q_101 := Eval native_compute in q_101_def.
Definition q_102_def := q_suc q_101.
Time Definition q_102 := Eval native_compute in q_102_def.
Definition q_103_def := q_suc q_102.
Time Definition q_103 := Eval native_compute in q_103_def.
Definition q_104_def := q_suc q_103.
Time Definition q_104 := Eval native_compute in q_104_def.
Definition q_105_def := q_suc q_104.
Time Definition q_105 := Eval native_compute in q_105_def.
Definition q_106_def := q_suc q_105.
Time Definition q_106 := Eval native_compute in q_106_def.
Definition q_107_def := q_suc q_106.
Time Definition q_107 := Eval native_compute in q_107_def.
Definition q_108_def := q_suc q_107.
Time Definition q_108 := Eval native_compute in q_108_def.
Definition q_109_def := q_suc q_108.
Time Definition q_109 := Eval native_compute in q_109_def.
Definition q_110_def := q_suc q_109.
Time Definition q_110 := Eval native_compute in q_110_def.
Definition q_111_def := q_suc q_110.
Time Definition q_111 := Eval native_compute in q_111_def.
Definition q_112_def := q_suc q_111.
Time Definition q_112 := Eval native_compute in q_112_def.
Definition q_113_def := q_suc q_112.
Time Definition q_113 := Eval native_compute in q_113_def.
Definition q_114_def := q_suc q_113.
Time Definition q_114 := Eval native_compute in q_114_def.
Definition q_115_def := q_suc q_114.
Time Definition q_115 := Eval native_compute in q_115_def.
Definition q_116_def := q_suc q_115.
Time Definition q_116 := Eval native_compute in q_116_def.
Definition q_117_def := q_suc q_116.
Time Definition q_117 := Eval native_compute in q_117_def.
Definition q_118_def := q_suc q_117.
Time Definition q_118 := Eval native_compute in q_118_def.
Definition q_119_def := q_suc q_118.
Time Definition q_119 := Eval native_compute in q_119_def.
Definition q_120_def := q_suc q_119.
Time Definition q_120 := Eval native_compute in q_120_def.
Definition q_121_def := q_suc q_120.
Time Definition q_121 := Eval native_compute in q_121_def.
Definition q_122_def := q_suc q_121.
Time Definition q_122 := Eval native_compute in q_122_def.
Definition q_123_def := q_suc q_122.
Time Definition q_123 := Eval native_compute in q_123_def.
Definition q_124_def := q_suc q_123.
Time Definition q_124 := Eval native_compute in q_124_def.
Definition q_125_def := q_suc q_124.
Time Definition q_125 := Eval native_compute in q_125_def.
Definition q_126_def := q_suc q_125.
Time Definition q_126 := Eval native_compute in q_126_def.
Definition q_127_def := q_suc q_126.
Time Definition q_127 := Eval native_compute in q_127_def.
Definition q_128_def := q_suc q_127.
Time Definition q_128 := Eval native_compute in q_128_def.
Definition q_129_def := q_suc q_128.
Time Definition q_129 := Eval native_compute in q_129_def.
Definition q_130_def := q_suc q_129.
Time Definition q_130 := Eval native_compute in q_130_def.
Definition q_131_def := q_suc q_130.
Time Definition q_131 := Eval native_compute in q_131_def.
Definition q_132_def := q_suc q_131.
Time Definition q_132 := Eval native_compute in q_132_def.
Definition q_133_def := q_suc q_132.
Time Definition q_133 := Eval native_compute in q_133_def.
Definition q_134_def := q_suc q_133.
Time Definition q_134 := Eval native_compute in q_134_def.
Definition q_135_def := q_suc q_134.
Time Definition q_135 := Eval native_compute in q_135_def.
Definition q_136_def := q_suc q_135.
Time Definition q_136 := Eval native_compute in q_136_def.
Definition q_137_def := q_suc q_136.
Time Definition q_137 := Eval native_compute in q_137_def.
Definition q_138_def := q_suc q_137.
Time Definition q_138 := Eval native_compute in q_138_def.
Definition q_139_def := q_suc q_138.
Time Definition q_139 := Eval native_compute in q_139_def.
Definition q_140_def := q_suc q_139.
Time Definition q_140 := Eval native_compute in q_140_def.
Definition q_141_def := q_suc q_140.
Time Definition q_141 := Eval native_compute in q_141_def.
Definition q_142_def := q_suc q_141.
Time Definition q_142 := Eval native_compute in q_142_def.
Definition q_143_def := q_suc q_142.
Time Definition q_143 := Eval native_compute in q_143_def.
Definition q_144_def := q_suc q_143.
Time Definition q_144 := Eval native_compute in q_144_def.
Definition q_145_def := q_suc q_144.
Time Definition q_145 := Eval native_compute in q_145_def.
Definition q_146_def := q_suc q_145.
Time Definition q_146 := Eval native_compute in q_146_def.
Definition q_147_def := q_suc q_146.
Time Definition q_147 := Eval native_compute in q_147_def.
Definition q_148_def := q_suc q_147.
Time Definition q_148 := Eval native_compute in q_148_def.
Definition q_149_def := q_suc q_148.
Time Definition q_149 := Eval native_compute in q_149_def.
Definition q_150_def := q_suc q_149.
Time Definition q_150 := Eval native_compute in q_150_def.
Definition q_151_def := q_suc q_150.
Time Definition q_151 := Eval native_compute in q_151_def.
Definition q_152_def := q_suc q_151.
Time Definition q_152 := Eval native_compute in q_152_def.
Definition q_153_def := q_suc q_152.
Time Definition q_153 := Eval native_compute in q_153_def.
Definition q_154_def := q_suc q_153.
Time Definition q_154 := Eval native_compute in q_154_def.
Definition q_155_def := q_suc q_154.
Time Definition q_155 := Eval native_compute in q_155_def.
Definition q_156_def := q_suc q_155.
Time Definition q_156 := Eval native_compute in q_156_def.
Definition q_157_def := q_suc q_156.
Time Definition q_157 := Eval native_compute in q_157_def.
Definition q_158_def := q_suc q_157.
Time Definition q_158 := Eval native_compute in q_158_def.
Definition q_159_def := q_suc q_158.
Time Definition q_159 := Eval native_compute in q_159_def.
Definition q_160_def := q_suc q_159.
Time Definition q_160 := Eval native_compute in q_160_def.
Definition q_161_def := q_suc q_160.
Time Definition q_161 := Eval native_compute in q_161_def.
Definition q_162_def := q_suc q_161.
Time Definition q_162 := Eval native_compute in q_162_def.
Definition q_163_def := q_suc q_162.
Time Definition q_163 := Eval native_compute in q_163_def.
Definition q_164_def := q_suc q_163.
Time Definition q_164 := Eval native_compute in q_164_def.
Definition q_165_def := q_suc q_164.
Time Definition q_165 := Eval native_compute in q_165_def.
Definition q_166_def := q_suc q_165.
Time Definition q_166 := Eval native_compute in q_166_def.
Definition q_167_def := q_suc q_166.
Time Definition q_167 := Eval native_compute in q_167_def.
Definition q_168_def := q_suc q_167.
Time Definition q_168 := Eval native_compute in q_168_def.
Definition q_169_def := q_suc q_168.
Time Definition q_169 := Eval native_compute in q_169_def.
Definition q_170_def := q_suc q_169.
Time Definition q_170 := Eval native_compute in q_170_def.
Definition q_171_def := q_suc q_170.
Time Definition q_171 := Eval native_compute in q_171_def.
Definition q_172_def := q_suc q_171.
Time Definition q_172 := Eval native_compute in q_172_def.
Definition q_173_def := q_suc q_172.
Time Definition q_173 := Eval native_compute in q_173_def.
Definition q_174_def := q_suc q_173.
Time Definition q_174 := Eval native_compute in q_174_def.
Definition q_175_def := q_suc q_174.
Time Definition q_175 := Eval native_compute in q_175_def.
Definition q_176_def := q_suc q_175.
Time Definition q_176 := Eval native_compute in q_176_def.
Definition q_177_def := q_suc q_176.
Time Definition q_177 := Eval native_compute in q_177_def.
Definition q_178_def := q_suc q_177.
Time Definition q_178 := Eval native_compute in q_178_def.
Definition q_179_def := q_suc q_178.
Time Definition q_179 := Eval native_compute in q_179_def.
Definition q_180_def := q_suc q_179.
Time Definition q_180 := Eval native_compute in q_180_def.
Definition q_181_def := q_suc q_180.
Time Definition q_181 := Eval native_compute in q_181_def.
Definition q_182_def := q_suc q_181.
Time Definition q_182 := Eval native_compute in q_182_def.
Definition q_183_def := q_suc q_182.
Time Definition q_183 := Eval native_compute in q_183_def.
Definition q_184_def := q_suc q_183.
Time Definition q_184 := Eval native_compute in q_184_def.
Definition q_185_def := q_suc q_184.
Time Definition q_185 := Eval native_compute in q_185_def.
Definition q_186_def := q_suc q_185.
Time Definition q_186 := Eval native_compute in q_186_def.
Definition q_187_def := q_suc q_186.
Time Definition q_187 := Eval native_compute in q_187_def.
Definition q_188_def := q_suc q_187.
Time Definition q_188 := Eval native_compute in q_188_def.
Definition q_189_def := q_suc q_188.
Time Definition q_189 := Eval native_compute in q_189_def.
Definition q_190_def := q_suc q_189.
Time Definition q_190 := Eval native_compute in q_190_def.
Definition q_191_def := q_suc q_190.
Time Definition q_191 := Eval native_compute in q_191_def.
Definition q_192_def := q_suc q_191.
Time Definition q_192 := Eval native_compute in q_192_def.
Definition q_193_def := q_suc q_192.
Time Definition q_193 := Eval native_compute in q_193_def.
Definition q_194_def := q_suc q_193.
Time Definition q_194 := Eval native_compute in q_194_def.
Definition q_195_def := q_suc q_194.
Time Definition q_195 := Eval native_compute in q_195_def.
Definition q_196_def := q_suc q_195.
Time Definition q_196 := Eval native_compute in q_196_def.
Definition q_197_def := q_suc q_196.
Time Definition q_197 := Eval native_compute in q_197_def.
Definition q_198_def := q_suc q_197.
Time Definition q_198 := Eval native_compute in q_198_def.
Definition q_199_def := q_suc q_198.
Time Definition q_199 := Eval native_compute in q_199_def.
Definition q_200_def := q_suc q_199.
Time Definition q_200 := Eval native_compute in q_200_def.


Lemma iter_S{A}(f:A->A)(x x0:A) n:
  x0 = Nat.iter n f x ->
  f x0 = Nat.iter (S n) f x.
Proof.
  intro H.
  rewrite H.
  reflexivity.
Qed.

Ltac q_rw q_x q_x_def :=
  assert (H:q_x = q_x_def) by (native_cast_no_check (eq_refl q_x));
  rewrite H; unfold q_x_def; clear H; apply iter_S.

Lemma q_200_spec: q_200 = Nat.iter 200 q_suc q_0.
q_rw q_200 q_200_def.
q_rw q_199 q_199_def.
q_rw q_198 q_198_def.
q_rw q_197 q_197_def.
q_rw q_196 q_196_def.
q_rw q_195 q_195_def.
q_rw q_194 q_194_def.
q_rw q_193 q_193_def.
q_rw q_192 q_192_def.
q_rw q_191 q_191_def.
q_rw q_190 q_190_def.
q_rw q_189 q_189_def.
q_rw q_188 q_188_def.
q_rw q_187 q_187_def.
q_rw q_186 q_186_def.
q_rw q_185 q_185_def.
q_rw q_184 q_184_def.
q_rw q_183 q_183_def.
q_rw q_182 q_182_def.
q_rw q_181 q_181_def.
q_rw q_180 q_180_def.
q_rw q_179 q_179_def.
q_rw q_178 q_178_def.
q_rw q_177 q_177_def.
q_rw q_176 q_176_def.
q_rw q_175 q_175_def.
q_rw q_174 q_174_def.
q_rw q_173 q_173_def.
q_rw q_172 q_172_def.
q_rw q_171 q_171_def.
q_rw q_170 q_170_def.
q_rw q_169 q_169_def.
q_rw q_168 q_168_def.
q_rw q_167 q_167_def.
q_rw q_166 q_166_def.
q_rw q_165 q_165_def.
q_rw q_164 q_164_def.
q_rw q_163 q_163_def.
q_rw q_162 q_162_def.
q_rw q_161 q_161_def.
q_rw q_160 q_160_def.
q_rw q_159 q_159_def.
q_rw q_158 q_158_def.
q_rw q_157 q_157_def.
q_rw q_156 q_156_def.
q_rw q_155 q_155_def.
q_rw q_154 q_154_def.
q_rw q_153 q_153_def.
q_rw q_152 q_152_def.
q_rw q_151 q_151_def.
q_rw q_150 q_150_def.
q_rw q_149 q_149_def.
q_rw q_148 q_148_def.
q_rw q_147 q_147_def.
q_rw q_146 q_146_def.
q_rw q_145 q_145_def.
q_rw q_144 q_144_def.
q_rw q_143 q_143_def.
q_rw q_142 q_142_def.
q_rw q_141 q_141_def.
q_rw q_140 q_140_def.
q_rw q_139 q_139_def.
q_rw q_138 q_138_def.
q_rw q_137 q_137_def.
q_rw q_136 q_136_def.
q_rw q_135 q_135_def.
q_rw q_134 q_134_def.
q_rw q_133 q_133_def.
q_rw q_132 q_132_def.
q_rw q_131 q_131_def.
q_rw q_130 q_130_def.
q_rw q_129 q_129_def.
q_rw q_128 q_128_def.
q_rw q_127 q_127_def.
q_rw q_126 q_126_def.
q_rw q_125 q_125_def.
q_rw q_124 q_124_def.
q_rw q_123 q_123_def.
q_rw q_122 q_122_def.
q_rw q_121 q_121_def.
q_rw q_120 q_120_def.
q_rw q_119 q_119_def.
q_rw q_118 q_118_def.
q_rw q_117 q_117_def.
q_rw q_116 q_116_def.
q_rw q_115 q_115_def.
q_rw q_114 q_114_def.
q_rw q_113 q_113_def.
q_rw q_112 q_112_def.
q_rw q_111 q_111_def.
q_rw q_110 q_110_def.
q_rw q_109 q_109_def.
q_rw q_108 q_108_def.
q_rw q_107 q_107_def.
q_rw q_106 q_106_def.
q_rw q_105 q_105_def.
q_rw q_104 q_104_def.
q_rw q_103 q_103_def.
q_rw q_102 q_102_def.
q_rw q_101 q_101_def.
q_rw q_100 q_100_def.
q_rw q_99 q_99_def.
q_rw q_98 q_98_def.
q_rw q_97 q_97_def.
q_rw q_96 q_96_def.
q_rw q_95 q_95_def.
q_rw q_94 q_94_def.
q_rw q_93 q_93_def.
q_rw q_92 q_92_def.
q_rw q_91 q_91_def.
q_rw q_90 q_90_def.
q_rw q_89 q_89_def.
q_rw q_88 q_88_def.
q_rw q_87 q_87_def.
q_rw q_86 q_86_def.
q_rw q_85 q_85_def.
q_rw q_84 q_84_def.
q_rw q_83 q_83_def.
q_rw q_82 q_82_def.
q_rw q_81 q_81_def.
q_rw q_80 q_80_def.
q_rw q_79 q_79_def.
q_rw q_78 q_78_def.
q_rw q_77 q_77_def.
q_rw q_76 q_76_def.
q_rw q_75 q_75_def.
q_rw q_74 q_74_def.
q_rw q_73 q_73_def.
q_rw q_72 q_72_def.
q_rw q_71 q_71_def.
q_rw q_70 q_70_def.
q_rw q_69 q_69_def.
q_rw q_68 q_68_def.
q_rw q_67 q_67_def.
q_rw q_66 q_66_def.
q_rw q_65 q_65_def.
q_rw q_64 q_64_def.
q_rw q_63 q_63_def.
q_rw q_62 q_62_def.
q_rw q_61 q_61_def.
q_rw q_60 q_60_def.
q_rw q_59 q_59_def.
q_rw q_58 q_58_def.
q_rw q_57 q_57_def.
q_rw q_56 q_56_def.
q_rw q_55 q_55_def.
q_rw q_54 q_54_def.
q_rw q_53 q_53_def.
q_rw q_52 q_52_def.
q_rw q_51 q_51_def.
q_rw q_50 q_50_def.
q_rw q_49 q_49_def.
q_rw q_48 q_48_def.
q_rw q_47 q_47_def.
q_rw q_46 q_46_def.
q_rw q_45 q_45_def.
q_rw q_44 q_44_def.
q_rw q_43 q_43_def.
q_rw q_42 q_42_def.
q_rw q_41 q_41_def.
q_rw q_40 q_40_def.
q_rw q_39 q_39_def.
q_rw q_38 q_38_def.
q_rw q_37 q_37_def.
q_rw q_36 q_36_def.
q_rw q_35 q_35_def.
q_rw q_34 q_34_def.
q_rw q_33 q_33_def.
q_rw q_32 q_32_def.
q_rw q_31 q_31_def.
q_rw q_30 q_30_def.
q_rw q_29 q_29_def.
q_rw q_28 q_28_def.
q_rw q_27 q_27_def.
q_rw q_26 q_26_def.
q_rw q_25 q_25_def.
q_rw q_24 q_24_def.
q_rw q_23 q_23_def.
q_rw q_22 q_22_def.
q_rw q_21 q_21_def.
q_rw q_20 q_20_def.
q_rw q_19 q_19_def.
q_rw q_18 q_18_def.
q_rw q_17 q_17_def.
q_rw q_16 q_16_def.
q_rw q_15 q_15_def.
q_rw q_14 q_14_def.
q_rw q_13 q_13_def.
q_rw q_12 q_12_def.
q_rw q_11 q_11_def.
q_rw q_10 q_10_def.
q_rw q_9 q_9_def.
q_rw q_8 q_8_def.
q_rw q_7 q_7_def.
q_rw q_6 q_6_def.
q_rw q_5 q_5_def.
q_rw q_4 q_4_def.
q_rw q_3 q_3_def.
q_rw q_2 q_2_def.
q_rw q_1 q_1_def.
reflexivity.
Time Qed.


Lemma q_200_WF:
  SearchQueue_WF (N.to_nat BB5_minus_one) q_200 root.
Proof.
  rewrite q_200_spec.
  generalize 200.
  intro n.
  induction n.
  - replace (Nat.iter 0 q_suc q_0) with q_0 by reflexivity.
    unfold q_0,q0.
    apply root_q_upd1_simplified_WF.
  - replace (Nat.iter (S n) q_suc q_0) with (q_suc (Nat.iter n q_suc q_0)) by (apply iter_S; reflexivity).
    remember (Nat.iter n q_suc q_0) as q.
    clear Heqq.
    unfold q_suc.
    apply SearchQueue_upds_spec.
    + apply IHn.
    + apply decider_all_spec.
Qed.


Lemma q_200_empty:
  q_200 = (nil,nil).
Proof.
  reflexivity.
Qed.

Lemma root_HTUB:
  TNF_Node_HTUB (N.to_nat BB5_minus_one) root.
Proof.
  epose proof q_200_WF.
  unfold SearchQueue_WF in H.
  rewrite q_200_empty in H.
  apply H.
  cbn.
  intros.
  contradiction.
Qed.

Lemma TM0_HTUB:
  HaltTimeUpperBound Σ (N.to_nat BB5_minus_one) (InitES Σ Σ0) (LE Σ (TM0)).
Proof.
  apply root_HTUB.
Qed.

Lemma allTM_HTUB:
  HaltTimeUpperBound Σ (N.to_nat BB5_minus_one) (InitES Σ Σ0) (fun _ => True).
Proof.
  unfold HaltTimeUpperBound.
  intros.
  eapply TM0_HTUB.
  2: apply H0.
  unfold LE.
  intros.
  right.
  reflexivity.
Qed.


Lemma BB5_upperbound:
  forall tm n0, HaltsAt Σ tm n0 (InitES Σ Σ0) -> n0 <= N.to_nat BB5_minus_one.
Proof.
  intros tm n0.
  apply allTM_HTUB.
  trivial.
Qed.

Lemma BB5_value:
  BB5_value_statement.
Proof.
  unfold BB5_value_statement.
  split.
  - intros tm n0 H.
    invst H.
    epose proof (allTM_HTUB _ _ _ H0) as H1.
    Unshelve. 2: cbn; trivial.
    unfold BB5.
    unfold BB5_minus_one in H1.
    lia.
  - destruct BB5_lower_bound as [tm H].
    exists tm.
    replace (N.to_nat BB5) with (S (N.to_nat BB5_minus_one)).
    1: ctor; apply H.
    unfold BB5_minus_one,BB5. lia.
Qed.

Print Assumptions BB5_value.