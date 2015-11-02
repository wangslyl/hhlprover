theory goal 
	imports "processDef"
begin

(*The safety property to prove.*)
definition safeProp :: fform where
"safeProp == (plant_v1_1 [+](Con Real 2)) [<] (Con Real 0.05) [&] (plant_v1_1 [+] (Con Real 2)) [>] (Con Real -0.05)"

(*The system clock is always positive.*)
axiomatization where
Clock : "\<forall> s. (t [\<ge>] Con Real 0) s"


(*The following lists the constraints for solving the differential invariants for the 
differential equations.*)
(*The invariant guarantees the postcondition.*)
definition cons1 :: fform where 
"cons1 \<equiv> ((t [\<ge>]Con Real 0 [&] t [\<le>] Con Real 0.128 [&] Inv) [\<longrightarrow>]  safeProp)"
(*Initialization:the initial state guarantees the invariant;
and Computation: the computation guarantees the invariant.*)
definition cons2 :: fform where 
"cons2 \<equiv> ((plant_v1_1[=](Con Real -2) [&] plant_m1_1[=](Con Real 1250) 
    [&] control_1[=](Con Real 4055/2) [&] t[=](Con Real 0)) [\<longrightarrow>] Inv)"
(*The core parts: the discrete computation and differential equations garantee the invariants. *)
definition cons31 :: fform where
"cons31 == \<lambda> s. ((t [=]Con Real 16 / 125 [&] Inv) s \<longrightarrow> Inv (\<lambda>(y, i). if y = ''plant_t'' \<and> i = R then evalE (Con Real 0) s else s (y, i)))" 

definition cons32 :: fform where
"cons32 == \<lambda> s. (Inv s \<longrightarrow>
               Inv (\<lambda>(y, i). if (y = ''control_1'' \<and> i = R)
                       then (evalE (plant_m1_1 [*]
                                   (Con Real 811 / 500 [-] Con Real 1 / 100 [*] (control_1 [**] plant_m1_1 [-] Con Real 811 / 500) [-]
                                    Con Real 3 / 5 [*] (plant_v1_1 [+] Con Real 2)))
                             s)
                       else s (y, i)))" 
definition cons4 :: fform where 
"cons4 \<equiv>  exeFlow(PC_Diff11) (Inv)  [\<longrightarrow>]  Inv"
definition cons5 :: fform where 
"cons5 \<equiv>  exeFlow(PC_Diff22) (Inv)  [\<longrightarrow>]  Inv"

(*Put this whole constraint to the differential invariant generator.*)
lemma allCons: "\<forall> s. ( cons1 [&] cons2 [&] cons31 [&] cons32 [&] cons4 [&] cons5) s"
apply (simp add: cons1_def)
apply (simp add: cons2_def)
apply (simp add: cons4_def)
apply (simp add: cons5_def)
apply (simp add: safeProp_def)
(*
apply inv_oracle_SOS
done
*)
(**You can uncomment the above lines, if you have  Mathematica, Matlab, Yalmip and SDPT3 installed. "Sorry" will go away.**)
sorry

lemma constraint11: "\<forall> s. (t [\<ge>] Con Real 0 [&] t [\<le>] Con Real 16 / 125 [&] Inv) s \<longrightarrow> safeProp s"
apply (cut_tac allCons)
apply (simp add:cons1_def)
by (metis fAnd_def fImp_def)


lemma constraint1: "\<forall> s. (t [\<le>]Con Real 16 / 125 [&] Inv) s \<longrightarrow> safeProp s"
apply (cut_tac allCons)
apply (cut_tac Clock)
by (metis constraint11 fAnd_def)




lemma constraint2: "\<forall> s. (plant_v1_1[=](Con Real -2) [&] plant_m1_1[=](Con Real 1250) 
    [&] control_1[=](Con Real 4055/2) [&] t[=](Con Real 0)) s \<longrightarrow> Inv s"
apply (cut_tac allCons)
apply (simp add:cons2_def)
by (metis fAnd_def fImp_def)


lemma constraint31: "\<forall> s. ((t [=]Con Real 16 / 125 [&] Inv) s \<longrightarrow> Inv (\<lambda>(y, i). if y = ''plant_t'' \<and> i = R then evalE (Con Real 0) s else s (y, i)))"
apply (cut_tac allCons)
apply (simp add:cons31_def) 
by (metis (erased, lifting) fAnd_def)


lemma constraint32: "\<forall> s. (Inv s \<longrightarrow>
               Inv (\<lambda>(y, i). if (y = ''control_1'' \<and> i = R)
                       then (evalE (plant_m1_1 [*]
                                   (Con Real 811 / 500 [-] Con Real 1 / 100 [*] (control_1 [**] plant_m1_1 [-] Con Real 811 / 500) [-]
                                    Con Real 3 / 5 [*] (plant_v1_1 [+] Con Real 2)))
                             s)
                       else s (y, i)))"
apply (cut_tac allCons)
apply (simp add:cons32_def) 
by (metis (no_types, lifting) fAnd_def)



lemma constraint4: "\<forall> s.  exeFlow(PC_Diff11) (Inv) s  \<longrightarrow>  Inv s"
apply (cut_tac allCons)
apply (simp add:cons4_def)
by (metis fAnd_def fImp_def)


lemma constraint5: "\<forall> s.  exeFlow(PC_Diff22) (Inv) s  \<longrightarrow>  Inv s"
apply (cut_tac allCons)
apply (simp add:cons5_def)
by (metis fAnd_def fImp_def)


declare elE_def [simp del]
 

(*Goal for the whole process.*)
lemma goal : "{fTrue} PP {safeProp; (elE 0 [[|]] (almost safeProp))}"
(*mono*)
apply (cut_tac px="fTrue" and qx="t [\<le>] Con Real 16 / 125 [&] Inv" and Hx="(elE 0 [[|]] (almost (t [\<le>] Con Real 16 / 125 [&] Inv)))" in ConsequenceRule, auto)
prefer 2
apply (cut_tac constraint1, auto)
prefer 2
apply (cut_tac constraint1, auto)
apply (simp add:dOr_def almost_def, auto)
apply metis
apply (simp add:PP_def PC_Init_def PD_Init_def)
(*separate into intialization and repetitive control*)
apply (cut_tac m = "((plant_v1_1[=](Con Real -2)) [&] (plant_m1_1[=](Con Real 1250)) [&] (control_1[=](Con Real 2027.5)) [&] (t[=](Con Real 0)))" 
           and  H = "elE 0"  and  G="(elE 0 [[|]] (almost (t [\<le>] Con Real 16 / 125 [&] Inv)))"  in SequentialRule, auto)
(*Init*)
apply (cut_tac m = "((plant_v1_1[=]Con (Real -2)) [&] (plant_m1_1[=]Con (Real 1250)))" 
     and  H = "elE 0"  and  G = "elE 0" in SequentialRule, auto)
apply (cut_tac m = "plant_v1_1[=]Con Real - 2"  and  H = "elE 0" and  G = "elE 0" in SequentialRule, auto)
apply (rule AssignRRule, auto) apply (simp add:fEqual_def)
apply (cut_tac m = "plant_v1_1[=]Con Real - 2 [&] plant_m1_1[=]Con Real 1250" 
   and  H = "elE 0" and  G = "elE 0" in SequentialRule, auto)
apply (rule AssignRRule, auto) apply (simp add:fAnd_def fEqual_def)
apply (rule AssignRRule, auto) apply (simp add:fAnd_def fEqual_def)
apply (simp add:elE_def chop_def)+
apply (cut_tac m = "((plant_v1_1[=](Con Real -2)) [&] (plant_m1_1[=](Con Real 1250)) [&] (control_1[=](Con Real 2027.5)))" 
           and  H = "elE 0" and  G = "elE 0" in SequentialRule, auto)
apply (rule AssignRRule, auto) apply (simp add:fAnd_def fEqual_def)
apply (rule AssignRRule, auto) apply (simp add:fAnd_def fEqual_def)
apply (simp add:elE_def chop_def)+
prefer 2
apply (simp add:elE_def dOr_def chop_def)
(*Rep Part*)
apply (cut_tac px="Inv [&] t[=](Con Real 0) [&] t [\<le>] Con Real 16 / 125" and qx="Inv [&] t[=](Con Real 0) [&] t [\<le>] Con Real 16 / 125" and Hx="(elE 0 [[|]] (almost (t [\<le>] Con Real 16 / 125 [&] Inv)))" in ConsequenceRule,auto)
prefer 2
apply (cut_tac constraint2, auto) apply (simp add:fAnd_def fLessEqual_def fOr_def fLess_def fEqual_def)
prefer 2
apply (simp add:fAnd_def fLessEqual_def fOr_def fLess_def)
prefer 2
apply (simp add:elE_def dOr_def)
apply (rule RepetitionRule, auto)
apply (cut_tac P = "(RVar ''plant_t''[\<le>]Con Real 16 / 125 [&] Inv)"
      and h = h and n = n and nd = m in chopfor, auto)
apply (simp add:Inv3_def)
apply (cut_tac m = "t [=] Con Real 16 / 125 [&] Inv" and 
    H = "(elE 0 [[|]] (almost (t [\<le>] Con Real 16 / 125 [&] Inv)))" and  
  G= "elE 0" in  SequentialRule, auto)
prefer 2
apply (simp add: PD_Rep_def)
apply (cut_tac m = "t [=] Con Real 0 [&] Inv" and 
    H = "elE 0" and  G= "elE 0" in  SequentialRule, auto)
apply (rule AssignRRule, auto)
apply (cut_tac constraint31, auto)
 apply (simp add:fAnd_def fLessEqual_def fOr_def fLess_def fEqual_def)
apply (rule AssignRRule, auto)
apply (cut_tac constraint32)
 apply (simp add:fAnd_def fLessEqual_def fOr_def fLess_def fEqual_def)
using control_1_def plant_m1_1_def plant_v1_1_def 
apply presburger
apply (simp add:elE_def chop_def)
prefer 2 
apply (simp add:dOr_def elE_def)  apply (simp add:fAnd_def fLessEqual_def fOr_def fLess_def fEqual_def chop_def)
(*Plant Part*)
apply (simp add:PC_Difff_def)
apply (rule ConditionGRule, auto) 
apply (simp add:PC_Diff11_def Inv1_def)
apply (rule ContinuousRuleGT, auto)
apply (simp add:fLess_def fAnd_def fEqual_def) 
apply (simp add:fAnd_def)
apply (simp add:fAnd_def, auto)
apply (cut_tac e = "RVar ''plant_t''" and f = "Con Real 16 / 125" in Lessc)
apply (cut_tac e = "RVar ''plant_t''" and f = "Con Real 16 / 125" in notLess, auto)
apply (simp add:fGreaterEqual_def fLessEqual_def fOr_def fNot_def fAnd_def) 
apply (cut_tac constraint4)
apply (simp add:PC_Diff11_def Inv1_def)
apply (simp add:elE_def dOr_def)
apply (simp add:dOr_def)
apply (simp add:fAnd_def almost_def) 
apply metis
apply (simp add:PC_Diff22_def Inv2_def)
apply (rule ContinuousRuleGT, auto)
apply (simp add:fLess_def fAnd_def fEqual_def) 
apply (simp add:fAnd_def)
apply (simp add:fAnd_def, auto)
apply (cut_tac e = "RVar ''plant_t''" and f = "Con Real 16 / 125" in Lessc)
apply (cut_tac e = "RVar ''plant_t''" and f = "Con Real 16 / 125" in notLess, auto)
apply (simp add:fGreaterEqual_def fLessEqual_def fOr_def fNot_def fAnd_def) 
apply (cut_tac constraint5)
apply (simp add:PC_Diff22_def Inv2_def)
apply (simp add:elE_def dOr_def)
apply (simp add:dOr_def)
apply (simp add:fAnd_def almost_def) 
apply metis
done




end
