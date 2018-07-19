header {* Abstract syntax for Hybrid CSP. *}

theory HHL_SL
  imports  op_SL
begin

type_synonym now_dash = real
type_synonym dform = "history => now \<Rightarrow> now_dash \<Rightarrow> bool"

definition semd :: "history \<Rightarrow> now \<Rightarrow> now_dash  \<Rightarrow> dform \<Rightarrow> bool" ("_, [_, _] |= _"  50) where
"h, [n, m] |= H == (H h n m)"

(* One axiom stating that the dform formula is only decided by the interval between now and now_dash*)
axiomatization where
DC : "now \<le> now' \<Longrightarrow>(\<forall> t. t> now & t< now'\<longrightarrow> h t = h' t) \<Longrightarrow> (df :: dform) h now now' = df h' now now'"



section
{*Duration Calculus operators and lemmas proved.*}
(*Special assertions \<and> lemmas proved*)

(*almost P, P holds almost everywhere over the interval.*)
definition almost :: "fform \<Rightarrow> dform" where
(*"almost P \<equiv> % h n nd. (nd-n>0) & (\<not>(\<exists> a b.(n\<le>a & a<b & b\<le>nd) & (\<forall> t. t>a & t<b \<longrightarrow> \<not>P(h(t)))))"*)
(*An alternative definition of almost*)
"almost P \<equiv> % h n nd. (nd-n>0) &  (\<forall>a\<ge>n. \<forall>b\<le>nd. a < b \<longrightarrow> (\<exists>t. t>a \<and> t<b \<and> P(h(t))))"
definition chop :: "dform \<Rightarrow> dform \<Rightarrow> dform"  ("_[^]_" 80)
where
"chop H M \<equiv> % h n nd. (\<exists> nm. (nm \<ge> n \<and> nm \<le> nd \<and> (H h n nm) \<and> (M h nm nd)))"

(*The length of the interval l is equal to, greater than, less than T.*)
definition elE :: "real \<Rightarrow> dform" where
"elE T \<equiv> % h n nd. (nd-n) = T"
definition elG :: "real \<Rightarrow> dform" where
"elG T \<equiv> % h n nd. (nd-n) > T"
definition elL :: "real \<Rightarrow> dform" where
"elL T \<equiv> % h n nd. (nd-n) < T"

definition dAnd :: "dform \<Rightarrow> dform \<Rightarrow> dform"  (infixl "[[&]]"  79) where
"P [[&]] Q == % h n m. P h n m \<and> Q h n m"
definition dOr :: "dform \<Rightarrow> dform \<Rightarrow> dform"  (infixl "[[|]]" 79) where
"P [[|]] Q == % h n m. P h n m \<or> Q h n m"
definition dNot :: "dform \<Rightarrow> dform"  ("[[\<not>]]_" 79) where
"[[\<not>]]P == % h n m. \<not> P h n m"
definition dImp :: "dform \<Rightarrow> dform \<Rightarrow> dform"  (infixl "[[\<longrightarrow>]]" 79) where
"P [[\<longrightarrow>]] Q == % h n m. P h n m \<longrightarrow> Q h n m"

declare almost_def [simp]
declare chop_def [simp]
declare elE_def [simp]
declare elG_def [simp]
declare elL_def [simp]

(*True holds almost everywhere.*)
lemma almostf : "\<forall> h n nd. nd-n\<le>0 \<or> almost fTrue h n nd"
apply (simp)
 by (metis dense le_iff_diff_le_0 not_le) 


(*almost P \<Leftrightarrow> chop almost P almost P*)
lemma chopfb : "((chop (almost P) (almost P)) h n nd \<Longrightarrow> (almost P) h n nd)"
apply (simp)
apply (rule conjI, auto)
by (metis (poly_guards_query) less_eq_real_def less_trans not_less)

lemma chopfor : "((chop (elE 0 [[|]]almost P) (elE 0 [[|]]almost P)) h n nd \<Longrightarrow> (elE 0 [[|]]almost P) h n nd)"
apply (simp add:dOr_def)
apply (rule disjCI, auto)
by (metis dual_order.refl le_cases less_eq_real_def less_imp_not_less less_trans linear neq_iff not_less)
 

lemma chopf : "((almost P) h n nd \<Longrightarrow> (chop (almost P) (almost P)) h n nd)"
apply (simp)
apply (rule_tac x = "(n+nd)/2" in exI, auto)
apply (metis (poly_guards_query) le_iff_diff_le_0 not_le real_less_half_sum)
by (metis less_diff_eq monoid_add_class.add.left_neutral real_gt_half_sum)


lemma chop0L : "chop (almost P) (elE 0) h n nd \<Longrightarrow> almost P h n nd"
by auto
lemma chop0R : " almost P h n nd \<longrightarrow> chop (almost P) (elE 0) h n nd"
by auto
(*Monotonicity: s \<Rightarrow> t \<Longrightarrow> almost s \<Rightarrow> almost t*)
lemma almostmono: "(\<forall> s. P s \<longrightarrow> Q s) \<Longrightarrow> (\<forall> h n nd. almost P h n nd \<longrightarrow> almost Q h n nd)"
apply (auto)
by (metis (full_types))

lemma almostint: "now<nowf \<Longrightarrow> \<forall> t. (t>now \<and> t<nowf) \<longrightarrow> P (f t) \<Longrightarrow> almost P f now nowf"
apply (auto)
by (metis le_less_trans less_le_trans of_rat_dense)

section{*Inference rules for hybird CSP: Hybrid Hoare Logic rules*}


(*Specification*)
definition Valid :: "fform => proc => fform \<Rightarrow> dform => bool" ("{_}_{_; _}" 80)
where "Valid p c q H == (\<forall> now h now' h' . semB c now h now' h' \<longrightarrow> p (h(now)) \<longrightarrow> (q (h'(now'))
\<and> H h' now now'))"
definition ValidP :: "fform \<Rightarrow>fform \<Rightarrow> procP => fform \<Rightarrow> fform \<Rightarrow> dform \<Rightarrow> dform \<Rightarrow> bool"
("{_, _}_{_, _; _, _}" 80)
where "ValidP pa pb c qa qb Ha Hb == (\<forall> nowp nowq fp fq nowp' nowq' fp' fq'. 
semBP c nowp fp nowq fq nowp' fp' nowq' fq'  \<longrightarrow> 
(pa) (fp(nowp)) \<longrightarrow>pb (fq(nowq)) \<longrightarrow> 
(qa (fp'(nowp'))\<and> qb (fq'(nowq'))\<and> (Ha fp' nowp nowp') \<and> (Hb fq' nowq nowq')))"

subsection{*Inference rules proved sound*} 


(*Skip rule*)
lemma SkipRule : "\<forall> s h now now'. (p s \<longrightarrow> q s) \<and> ((elE 0) h now now'\<longrightarrow> H h now now')
         \<Longrightarrow> {p} Skip {q; H}"
by (auto simp add:Valid_def)
 
(*Assignment rule*)
lemma AssignRRule  :" (\<forall> s. p s \<longrightarrow> (q (%(y, i). if (y=x\<and>i=R) then (evalE f s) else s(y, i))))
                   \<and> (\<forall> h now now'. ((elE 0) h now now'\<longrightarrow> H h now now')) ==>
       {p} ((RVar x) := f) {q; H}"
apply (simp add:Valid_def, auto)
done

(*Sequential rule*)
(*The proof is complicated because of the existence of chop operator.*)
lemma SequentialRule_aux : " {p} P {m; H} \<Longrightarrow> {m} Q {q; G} ==>
             {p} P;  Q {q; H [^] G}" 
apply  (simp add:Valid_def, auto)
apply (subgoal_tac "now \<le> now'a \<and> now'a \<le> now'\<and> H h' now now'a = H f' now now'a")
apply metis
apply (rule conjI)
apply (cut_tac P = "P" and now = now and  now'=now'a and f = "h" and f' = "f'" in sem1, simp)
apply metis
apply (rule conjI)
apply (cut_tac P = "Q" and now = now'a and  now'=now' and f = "f'" and f' = "h'" in sem1, simp)
apply metis
apply (rule DC)
apply (cut_tac P = "P" and now = now and  now'=now'a and f = "h" and f' = "f'" in sem1, simp)
apply metis
apply (subgoal_tac "\<forall>t. t < now'a \<or> t>now' \<longrightarrow> f' t = h' t")
apply metis
apply (cut_tac P = Q in  sem2, auto)
done

lemma SequentialRule : " {p} P {m; H} \<Longrightarrow> {m} Q {q; G} ==> (\<forall> h m n. (H [^] G) h m n \<longrightarrow> M h m n) \<Longrightarrow>
             {p} P;  Q {q; M}" 
apply (cut_tac P = P and  Q = Q  and  p = p and  q =q and m = m and H = H  and  G = G in  SequentialRule_aux, auto)
apply (simp add:Valid_def)
done


(*Conditional rule*)
lemma ConditionTRule : " ((\<forall> s. p s \<longrightarrow> ( b s)) \<and> {p} P {q; H})
             ==> {p} IF b P {q; H}"
apply (simp add:Valid_def, auto)
done

lemma ConditionFRule : " ((\<forall> s. p s \<longrightarrow> (q s \<and> (\<not>   b s))) \<and> (\<forall> h now now'. ((elE 0) h now now'\<longrightarrow> H h now now')))
                          ==> {p} IF b P {q; H}"
apply (simp add:Valid_def, auto)
done

lemma ConditionGRule : " {p [&] b} P {q; H} \<and> {p [&] ([\<not>]b)} Q {q; H}
             ==> {p} IFELSE b P Q{q; H}"
apply (simp add:Valid_def fAnd_def fNot_def, auto)
done

declare almost_def [simp del]
declare chop_def [simp del]
(*Assume v'=E is the differential equation for the continuous evolution.*)
(*This proof takes most effort for solving the invariant-related constraints, which will be passed to an 
external oracle for invariant generation in fact. So don't worry.*)
lemma ContinuousRule : 
"\<forall> s u. ( ( \<forall> y i.(y, i) \<noteq> (fst (v), snd (v)) \<longrightarrow> s (y, i) = u (y, i)) \<longrightarrow> (p s) \<longrightarrow> (p u)) \<and>
 ( \<forall> s.  Init s \<longrightarrow>  Inv s)
 \<and> (\<forall> s.  (p [&] (Inv) [&] ([\<not>]b)) s \<longrightarrow> q s)
 \<and> (\<forall> s. (exeFlow (<[v]:E&&Inv&b>) (Inv)) s \<longrightarrow> Inv s)
 \<and>  (\<forall> h now now'. ((elE 0) h now now' \<or> (almost (Inv [&] p  [&] b)) h now now') \<longrightarrow>
                  H h now now')
 ==> {Init [&] (p::fform)} <[v]:E&&Inv&(b)> {q; H}"
apply (simp add:Valid_def) apply clarify
apply (subgoal_tac "\<forall> t. t\<ge>now & t\<le>now' \<longrightarrow> exeFlow (<[v]:E&&Inv&b>) (Inv) (h'(t))")
prefer 2
apply (simp add:exeFlow_def)
apply (metis fAnd_def)
apply auto
apply (metis fAnd_def)
apply (subgoal_tac "(p [&] Inv) (\<lambda>(y, i). if y = fst v \<and> i = snd v 
 then Solution (<[v]:E&&Inv&b>) (h now) (now + d - now) else h now (y, i))")
apply (simp add:fAnd_def)+
apply (rule conjI, auto)
apply (subgoal_tac "\<forall> y i. (y, i) \<noteq> v \<longrightarrow> (h(now)) (y, i) = ((\<lambda>(y, i). if y = fst v \<and> i = snd v 
   then Solution (<[v]:E&&Inv&b>) (h now) (now + d - now) else h now (y, i))) (y, i)")
apply smt2
apply auto 
apply (subgoal_tac "exeFlow (<[v]:E&&Inv&b>) (Inv)
                    (\<lambda>(y, i). if y = fst v \<and> i = snd v 
        then Solution (<[v]:E&&Inv&b>) (h now) (now+d - now) else h now (y, i))")
apply (metis (no_types, lifting))
apply (drule_tac x = "now +d" in spec, auto)
apply (subgoal_tac "almost (Inv [&] p [&] b) 
(\<lambda>t. if t \<le> now + d \<and> now < t then \<lambda>(y, i). if y = fst v \<and> i = snd v 
then Solution (<[v]:E&&Inv&b>) (h now) (t - now) else h now (y, i) else h t) now (now+d)", auto)
apply (rule almostint, auto)
apply (simp add:fAnd_def)
apply (rule conjI)
apply (subgoal_tac "exeFlow (<[v]:E&&Inv&b>) (Inv)
                    (\<lambda>(y, i). if y = fst v \<and> i = snd v 
        then Solution (<[v]:E&&Inv&b>) (h now) (t - now) else h now (y, i))")
apply (metis (no_types, lifting)) 
apply (drule_tac x = "t" in spec, auto)
apply (subgoal_tac "\<forall> y i. (y, i) \<noteq> v \<longrightarrow> (h(now)) (y, i) = ((\<lambda>(y, i). if y = fst v \<and> i = snd v 
   then Solution (<[v]:E&&Inv&b>) (h now) (t - now) else h now (y, i))) (y, i)")
apply smt2
apply auto 
done

(*We simple extend the above rule to the general case where the continuous are a list of variables not just one.
The proof can be given in the same way.*)
primrec notcontain :: "(string * typeid) \<Rightarrow> (string * typeid) list \<Rightarrow> bool" 
where
"notcontain a ([]) = True" |
"notcontain a (e # Elist) = (if a = e then False else (notcontain a Elist))"

axiomatization where ContinuousRuleGT:
" (\<forall> s. (p) s --> b s)
\<and> ( \<forall> s.  p s \<longrightarrow>  Inv s)
 \<and> (\<forall> s.  ((Inv) [&] (close (b)) [&] (close([\<not>]b))) s \<longrightarrow> q s)
 \<and> (\<forall> s. (exeFlow (<V:E&&Inv&b>) (Inv)) s \<longrightarrow> Inv s)
 \<and>  (\<forall> h now now'. ((elE 0) h now now' \<or> (almost (Inv [&]  close(b))) h now now') \<longrightarrow>
                  H h now now')
 ==> {p} <V:E&&Inv&(b)> {q; H}"

axiomatization where ContinuousRuleGF:
" \<forall> s. p s \<longrightarrow> (([\<not>] b) [&]q) s
 ==> {p} <V:E&&Inv&(b)> {q; elE 0}"

(*There are three rules for parallel  composition, which covers all the cases.*)
(*Parallel rule for the case without communication*)
lemma Parallel_aux : 
"  semBP (P || Q) nowp fp nowq fq nowp' fp' nowq' fq' \<Longrightarrow>
       \<forall>now h now' h'. semB P now h now' h' \<longrightarrow> pp (h now) \<longrightarrow> qp (h' now') \<and> Hp h' now now' \<Longrightarrow>
       \<forall>now h now' h'. semB Q now h now' h' \<longrightarrow> pq (h now) \<longrightarrow> qq (h' now') \<and> Hq h' now now' \<Longrightarrow>
       chanset P = {} \<Longrightarrow> chanset Q = {} \<Longrightarrow>
       pp (fp nowp) \<Longrightarrow> pq (fq nowq) \<Longrightarrow> qp (fp' nowp') \<and> qq (fq' nowq') \<and> Hp fp' nowp nowp' \<and> Hq fq' nowq nowq'"
apply (ind_cases " semBP (P || Q) nowp fp nowq fq nowp' fp' nowq' fq'")
apply metis
apply (simp add:chanset_def)+
done
 
lemma Parallel1Rule : "chanset P = {} \<and> chanset Q = {} \<Longrightarrow> {pp} P {qp; Hp} \<Longrightarrow> {pq} Q {qq; Hq}
                       \<Longrightarrow> {pp, pq} P||Q {qp, qq; Hp, Hq}"
apply (clarsimp simp:Valid_def ValidP_def)
apply (rule Parallel_aux)
apply simp+
done


(*Parallel rule for the case with communication at the end.*)
lemma Communication_aux: 
"  semBP (P; Cm (ch??(RVar x)) || Q; Cm (ch!!e)) nowp fp nowq fq nowp' fp' nowq' fq' \<Longrightarrow>
    \<forall> nowp nowq fp fq nowp' nowq' fp' fq'.
          semBP (P || Q) nowp fp nowq fq nowp' fp' nowq' fq' \<longrightarrow>
          px (fp nowp) \<longrightarrow> py (fq nowq) \<longrightarrow> qx (fp' nowp') \<and> qy (fq' nowq') \<and> Hx fp' nowp nowp' \<and> Hy fq' nowq nowq' \<Longrightarrow>
       \<forall>s. qx s \<longrightarrow> rx (\<lambda>(y, i). if y = x \<and> i = R then evalE e s else s (y, i)) \<Longrightarrow>
       \<forall>s. qy s \<longrightarrow> ry s \<Longrightarrow>
       \<forall>h n m. (Hx[^](elE 0 [[|]]almost qx)) h n m \<longrightarrow> Gx h n m \<Longrightarrow>
       \<forall>h n m. (Hy[^](elE 0 [[|]]almost qy)) h n m \<longrightarrow> Gy h n m \<Longrightarrow>      
       px (fp nowp) \<Longrightarrow> py (fq nowq) \<Longrightarrow> rx (fp' nowp') \<and> ry (fq' nowq') \<and> Gx fp' nowp nowp' \<and> Gy fq' nowq nowq'"
apply (ind_cases "semBP (P; Cm (ch??(RVar x)) || Q; Cm (ch!!e)) nowp fp nowq fq nowp' fp' nowq' fq'")
apply (simp add:chanset_def) 
apply (simp add:chanset_def) 
apply (subgoal_tac " qx (fp'a nowp'a) \<and> qy (fq'a nowq'a) \<and> Hx fp'a nowp nowp'a \<and> Hy fq'a nowq nowq'a")
prefer 2
apply metis
apply (rule conjI) 
apply (subgoal_tac "fp' nowp' = (\<lambda>(y, i). if y = x \<and> i = R then evalE e (fp'a nowp'a) else (fp'a nowp'a) (y, i))", simp)
apply (metis less_irrefl)
apply (rule conjI)
apply (metis max.cobounded1 max_def_raw not_less)
apply (rule conjI)
(*to prove GX*)
apply (subgoal_tac "(Hx[^](elE 0 [[|]] almost qx)) fp' nowp nowp'", simp)
apply (subgoal_tac "Hx fp' nowp nowp'a",simp)
prefer 2 
apply (subgoal_tac "Hx fp'a nowp nowp'a = Hx fp' nowp nowp'a", simp)
apply (rule DC)
apply (metis semB1)
apply (metis less_max_iff_disj less_not_sym)
apply (simp add:chop_def)
apply (rule_tac x = "nowp'a" in exI, simp)
apply (rule conjI)
apply (metis semB1)
apply (simp add:dOr_def)
apply (case_tac "max nowp'a nowq'a > nowp'a")
prefer 2 apply (rule disjI1) 
apply (metis less_eq_real_def max.cobounded1)
apply (rule disjI2)
apply (rule almostint, simp) 
apply (metis (no_types, lifting))
(*to prove Gy, just copy the proof for Gx with a little adaption*)
apply (subgoal_tac "(Hy[^](elE 0 [[|]] almost qy)) fq' nowq nowq'", simp)
apply (subgoal_tac "Hy fq' nowq nowq'a",simp)
prefer 2 
apply (subgoal_tac "Hy fq'a nowq nowq'a = Hy fq' nowq nowq'a", simp)
apply (rule DC)
apply (metis semB1)
apply (metis less_max_iff_disj less_not_sym)
apply (simp add:chop_def)
apply (rule_tac x = "nowq'a" in exI, simp)
apply (rule conjI)
apply (metis semB1)
apply (simp add:dOr_def)
apply (case_tac "max nowp'a nowq'a > nowq'a")
prefer 2 
apply (rule disjI1) 
apply (metis less_eq_real_def max.cobounded2)
apply (rule disjI2)
apply (rule almostint, simp) 
apply (subgoal_tac "qy (fq'a nowq'a)")
apply smt2
by metis


lemma CommunicationRule : 
  " ({px, py} (P || Q) {qx, qy; Hx, Hy}) \<Longrightarrow>  
   (\<forall> s. qx s \<longrightarrow> (rx (%(y, i). if (y=x\<and>i=R) then (evalE e s) else s(y, i))))
 \<and> (\<forall> s. qy s \<longrightarrow> ry s)
 \<and> (\<forall> h n m. (Hx[^](elE 0 [[|]]almost qx)) h n m \<longrightarrow> Gx h n m) \<and> 
   (\<forall> h n m. (Hy[^](elE 0 [[|]]almost qy)) h n m \<longrightarrow> Gy h n m)
  ==>
{px, py} (P;Cm (ch??(RVar (x))))||(Q; (Cm (ch!!e))) {rx, ry; Gx, Gy}"
apply (clarsimp simp:ValidP_def) 
apply (rule Communication_aux)
apply simp+ 
done


(*Parallel rule for the case with non-communication process at the end.*)
lemma Parallel2_aux : "semBP (P; U || Q; V) nowp fp nowq fq nowp' fp' nowq' fq' \<Longrightarrow>
        \<forall>nowp nowq fp fq nowp' nowq' fp' fq'.
          semBP (P || Q) nowp fp nowq fq nowp' fp' nowq' fq' \<longrightarrow>
          pp (fp nowp) \<longrightarrow> pq (fq nowq) \<longrightarrow> qp (fp' nowp') \<and> qq (fq' nowq') \<and> 
        Hp fp' nowp nowp' \<and> Hq fq' nowq nowq' \<Longrightarrow>
       \<forall>now h now' h'. semB U now h now' h' \<longrightarrow> qp (h now) \<longrightarrow> qu (h' now') \<and> Hu h' now now' \<Longrightarrow>
       \<forall>now h now' h'. semB V now h now' h' \<longrightarrow> qq (h now) \<longrightarrow> qv (h' now') \<and> Hv h' now now' \<Longrightarrow>
       chanset P \<noteq> {} \<Longrightarrow> chanset Q \<noteq> {} \<Longrightarrow> chanset U = {} \<Longrightarrow> chanset V = {} \<Longrightarrow>
       pp (fp nowp) \<Longrightarrow> pq (fq nowq) \<Longrightarrow> qu (fp' nowp') \<and> qv (fq' nowq') \<and> 
             (Hp[^]Hu) fp' nowp nowp' \<and> (Hq[^]Hv) fq' nowq nowq'"
apply (ind_cases "semBP (P; U || Q; V) nowp fp nowq fq nowp' fp' nowq' fq'")
apply (simp add:chanset_def)
prefer 2 apply (simp add:chanset_def)
prefer 2 apply (simp add:chanset_def)
apply (subgoal_tac "qp (fp'a nowp'a) \<and> qq (fq'a nowq'a) \<and> Hp fp'a nowp nowp'a \<and> Hq fq'a nowq nowq'a")
prefer 2
apply metis
apply (rule conjI) apply metis
apply (rule conjI) apply metis
apply (subgoal_tac "(Hu) fp' nowp'a nowp' ")
apply (subgoal_tac "(Hv) fq' nowq'a nowq'")
prefer 2 apply metis prefer 2 apply metis
apply (subgoal_tac " Hq fq' nowq nowq'a")
apply (subgoal_tac " Hp fp' nowp nowp'a ")
apply (rule conjI)
apply (unfold chop_def)
apply (metis sem1 semB1)
apply (metis sem1 semB1)
apply (subgoal_tac "Hp fp'a nowp nowp'a = Hp fp' nowp nowp'a", simp)
apply (rule DC)
apply (metis semB1)
apply (metis sem2)
apply (subgoal_tac " Hq fq'a nowq nowq'a =  Hq fq' nowq nowq'a", simp)
apply (rule DC)
apply (metis semB1)
apply (metis sem2)
done

lemma Parallel2Rule : "{pp, pq} P||Q {qp, qq; Hp, Hq}  \<Longrightarrow> chanset P \<noteq> {} \<and> chanset Q \<noteq> {} \<Longrightarrow> 
                          {qp} U {qu; Hu} \<Longrightarrow> {qq} V {qv; Hv} \<Longrightarrow> chanset U = {} \<and> chanset V = {} 
                       \<Longrightarrow> {pp, pq} P; U||Q; V {qu, qv; Hp [^] Hu, Hq [^] Hv}"
apply (clarsimp simp:Valid_def ValidP_def)
apply (rule Parallel2_aux)
apply simp+
done
 
(*Repetition rule*)

  
lemma Repetition_aux_1: " semB (P* NUM 0) now h now' h' ⟹
       ∀h n m. (H[^]H) h n m ⟶ H h n m ⟹
       ∀now h now' h'. semB P now h now' h' ⟶ Inv (h now) ⟶ Inv (h' now') ∧ H h' now now' ⟹
       Inv (h now) ⟹ Inv (h' now') ∧ (H h' now now' ∨ now' = now)"
  apply (ind_cases "semB (P* NUM 0) now h now' h'", auto)
  done
    
    
lemma Repetition_aux_2: " (⋀now h now' h'. semB (P* NUM N) now h now' h' ⟹ Inv (h now) ⟹ Inv (h' now') ∧ (H h' now now' ∨ now' = now)) ⟹
       semB (P* NUM Suc N) now h now' h' ⟹
       ∀h n m. (H[^]H) h n m ⟶ H h n m ⟹
       ∀now h now' h'. semB P now h now' h' ⟶ Inv (h now) ⟶ Inv (h' now') ∧ H h' now now' ⟹
       Inv (h now) ⟹ Inv (h' now') ∧ (H h' now now' ∨ now' = now)"
  apply (ind_cases "semB (P* NUM Suc N) now h now' h'")
  apply simp
  by (smt DC chop_def sem1 sem2)

lemma Repetition_aux: "semB (P* NUM N) now h now' h' ⟹ 
                     ∀h n m. (H[^]H) h n m ⟶ H h n m ⟹
                     ∀now h now' h'. semB P now h now' h' ⟶ Inv (h now) ⟶ Inv (h' now') ∧ H h' now now' ⟹
                     Inv (h now) ⟹ Inv (h' now') ∧ (H [[|]] (λh n nd. nd = n)) h' now now'"
apply (simp add:dOr_def)
apply (induction N arbitrary: now h now' h')
   apply (rule Repetition_aux_1) apply simp+
  apply (cut_tac P = P and N = N and now = now and h = h and h' = h' and Inv = Inv in Repetition_aux_2, auto)
    done

lemma RepetitionRule: "∀h n m. (H[^]H) h n m ⟶ H h n m ⟹ {Inv} P {Inv; H}  
                      ==>  {Inv} P*&&Inv {Inv; (H [[|]] (elE 0))} "
  apply (simp add:Valid_def) apply clarify 
  apply (rule Repetition_aux)
   apply simp+
  done

(*Join Rule*)
lemma JoinRule : "{p} P {m; H} ⟹ {p} Q {q; G} ==>
             {p} P [[ Q {m [|] q; H [[|]] G}"
  apply (simp add:Valid_def fOr_def dOr_def, auto)
    done


(*Consequence rule*)
lemma ConsequenceRule : "{px} P {qx; Hx} 
                  \<and> (\<forall> s. p s \<longrightarrow> px s) \<and> (\<forall> s. qx s \<longrightarrow> q s)
                  \<and> (\<forall> h n m. Hx h n m \<longrightarrow> H h n m)
            ==> {p} P {q; H}"
apply (simp add:Valid_def)
done

(*Case analysis rule*)
lemma CaseRule : "{p [&] pb} P {q; H} \<and> {(p [&] ([\<not>]pb))} P {q; H}
   ==> {p} P {q; H}"
apply (simp add:Valid_def fAnd_def fNot_def, auto)
apply metis+
done

end
