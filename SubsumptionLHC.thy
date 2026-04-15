theory SubsumptionLHC
  imports SyntacticRelationalAssertions
begin

text\<open> IMPORTANT!
  LHC assumes that post hyper-assertions are upward closed
\<close>

section \<open>Language & Semantics\<close>

type_synonym val = int

type_synonym  store = "nat \<Rightarrow> val"

subsection Language

datatype trm = 
  Val val
  | Var nat
  | Havoc
  | Op "val \<Rightarrow> val \<Rightarrow> val" "trm" "trm"
  | Assign nat "trm"
  | Seq "trm" "trm"  (infixl ";;" 60)
  | If "trm" "trm" "trm"
  | Skip
  | While "trm" "trm"



subsection Semantics

inductive big_sem :: "trm \<Rightarrow> store \<Rightarrow> val \<Rightarrow> store \<Rightarrow> bool"
  ("\<langle>_, _\<rangle> \<Down> \<langle>_, _\<rangle>" [51,0] 81)
  where
  SemSkip: "\<langle>Skip, \<sigma>\<rangle> \<Down> \<langle>v, \<sigma>\<rangle>"
| SemAssign: "\<langle>C, \<sigma>\<rangle> \<Down> \<langle>v, \<sigma>'\<rangle> \<Longrightarrow> \<langle>Assign x C, \<sigma>\<rangle> \<Down> \<langle>v, \<sigma>'(x := v)\<rangle>"
| SemSeq: "\<lbrakk> \<langle>C1, \<sigma>\<rangle> \<Down> \<langle>v1, \<sigma>'\<rangle>; \<langle>C2, \<sigma>'\<rangle> \<Down> \<langle>v2, \<sigma>''\<rangle> \<rbrakk> \<Longrightarrow> \<langle>Seq C1 C2, \<sigma>\<rangle> \<Down> \<langle>v, \<sigma>''\<rangle>"
| SemIfTrue: "\<lbrakk>\<langle>B, \<sigma>\<rangle> \<Down> \<langle>vb, \<sigma>'\<rangle>; vb \<noteq> 0; \<langle>C1, \<sigma>'\<rangle> \<Down> \<langle>v, \<sigma>''\<rangle>\<rbrakk> \<Longrightarrow> \<langle>If B C1 C2, \<sigma>\<rangle> \<Down> \<langle>v, \<sigma>''\<rangle>"
| SemIfFalse: "\<lbrakk>\<langle>B, \<sigma>\<rangle> \<Down> \<langle>vb, \<sigma>'\<rangle>; vb = 0; \<langle>C2, \<sigma>'\<rangle> \<Down> \<langle>v, \<sigma>''\<rangle>\<rbrakk> \<Longrightarrow> \<langle>If B C1 C2, \<sigma>\<rangle> \<Down> \<langle>v, \<sigma>''\<rangle>"
| SemWhileTrue: "\<lbrakk>\<langle>B, \<sigma>\<rangle> \<Down> \<langle>vb, \<sigma>'\<rangle>; vb \<noteq> 0; \<langle>C, \<sigma>'\<rangle> \<Down> \<langle>v, \<sigma>''\<rangle>; \<langle>While B C, \<sigma>''\<rangle> \<Down> \<langle>v', \<sigma>'''\<rangle> \<rbrakk> \<Longrightarrow> \<langle>While B C, \<sigma>\<rangle> \<Down> \<langle>v', \<sigma>'''\<rangle>"
| SemWhileFalse: "\<lbrakk>\<langle>B, \<sigma>\<rangle> \<Down> \<langle>vb, \<sigma>'\<rangle>; vb = 0\<rbrakk> \<Longrightarrow> \<langle>While B C, \<sigma>\<rangle> \<Down> \<langle>v, \<sigma>'\<rangle>"
| SemVal: "\<langle>Val v,\<sigma>\<rangle> \<Down> \<langle>v,\<sigma>\<rangle>"
| SemVar: "\<langle>Var x, \<sigma>\<rangle> \<Down> \<langle>\<sigma> x,\<sigma>\<rangle>"
| SemHavoc: "\<langle>Havoc, \<sigma>\<rangle> \<Down> \<langle>v, \<sigma>\<rangle>"
| SemOp: "\<lbrakk>\<langle>C1, \<sigma>\<rangle> \<Down> \<langle>v1, \<sigma>'\<rangle>; \<langle>C2, \<sigma>'\<rangle> \<Down> \<langle>v2, \<sigma>''\<rangle>\<rbrakk> \<Longrightarrow> \<langle>Op op C1 C2, \<sigma>\<rangle> \<Down> \<langle>op v1 v2,\<sigma>''\<rangle>"


section Logic 

type_synonym hyper_store = "nat \<Rightarrow> store"
type_synonym hyper_term = "(nat \<times> trm) list"
type_synonym hyper_return_value = "(nat \<times> val) list"

type_synonym hyper_assertion = "hyper_store \<Rightarrow> bool" 
type_synonym post_hyper_assertion = "hyper_return_value \<Rightarrow> hyper_store \<Rightarrow> bool" 


definition upward_closed :: "post_hyper_assertion \<Rightarrow> bool" where
"upward_closed Q = (\<forall>V V' S. (Q V S \<and> (\<forall>i\<in>(dom (map_of V)). (map_of V) i = (map_of V') i) \<longrightarrow> Q V' S))"


definition big_sem_hyper :: "hyper_term \<Rightarrow> hyper_store \<Rightarrow> hyper_return_value \<Rightarrow> hyper_store \<Rightarrow> bool"
("\<langle>_, _\<rangle> \<Down> \<langle>_, _\<rangle>" [51,0] 81)
where
"\<langle>Cs, S\<rangle> \<Down> \<langle>V, S'\<rangle> = (\<forall>i::nat. if i\<in>(dom (map_of Cs)) 
        then (\<exists>v C. map_of V i = (Some v) \<and> map_of Cs i = (Some C) \<and> \<langle>C, S i\<rangle> \<Down> \<langle>v, S' i\<rangle>) 
                           else S i = S' i \<and> map_of V i = None)"

definition imp :: "hyper_assertion \<Rightarrow> hyper_assertion \<Rightarrow> hyper_assertion" where
  "imp P1 P2 = (\<lambda>S. (P1 S \<longrightarrow> P2 S))"


definition wp :: "hyper_term \<Rightarrow> post_hyper_assertion \<Rightarrow> hyper_assertion" where
"wp Cs Q = (\<lambda>S. (\<forall>S' V. \<langle>Cs, S\<rangle> \<Down> \<langle>V, S'\<rangle> \<longrightarrow> Q V S'))"

definition hyper_hoare_triple :: "hyper_assertion \<Rightarrow> hyper_term \<Rightarrow> post_hyper_assertion \<Rightarrow> hyper_assertion"
 ("{_} [_] {_}" [51,0,0] 81) where
  "{P} [Cs] {Q} = (imp P (wp Cs Q))"


definition valid :: "hyper_assertion \<Rightarrow> bool"
("\<Turnstile>LHC _" [55] 55)
  where 
"\<Turnstile>LHC P = (\<forall>S. P S)"


section \<open>Subsumption by RHHL\<close>


text\<open>
  sp - stack pointer always points to the last (if vp is 1) or second to last (in other cases) position on the current operation stack
  vp - variables pointer always points to the first available position for program variables
\<close>
fun translate_program :: "trm \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat, val) stmt" where
Skip: "translate_program Skip sp vp = stmt.Havoc sp" |
Seq:"translate_program (Seq C1 C2) sp vp = stmt.Seq (stmt.Seq (translate_program C1 sp vp) (translate_program C2 sp vp)) (stmt.Havoc sp)" |
Val:"translate_program (Val v) sp vp = stmt.Assign sp (\<lambda>_.v)"|
Var:"translate_program (Var x) sp vp = stmt.Assign sp (\<lambda>\<sigma>. \<sigma> (vp + x))"|
Havoc:"translate_program Havoc sp vp = stmt.Havoc sp"|
Op:"translate_program (Op op C1 C2) sp vp = stmt.Seq (translate_program C1 sp vp)
                                    (stmt.Seq (translate_program C2 (Suc sp) vp) 
                                    (stmt.Seq (stmt.Assign sp (\<lambda>\<sigma>. op (\<sigma> sp) (\<sigma> (Suc sp)))) ((stmt.Assign (Suc sp) (\<lambda>\<sigma>. 0)))))"|
Assign:"translate_program (Assign x C) sp vp = stmt.Seq (translate_program C sp vp) (stmt.Assign (vp + x) (\<lambda>\<sigma>. (\<sigma> sp)))"|
If: "translate_program (If B C1 C2) sp vp = stmt.Seq (translate_program B sp vp) 
                                  (if_then_else (\<lambda>\<sigma>. (\<sigma> sp) \<noteq> 0) (translate_program C1 sp vp) (translate_program C2 sp vp))"|
While: "translate_program (While B C) sp vp = stmt.Seq (stmt.Seq (translate_program B sp vp) 
                                (while_cond (\<lambda>\<sigma>. (\<sigma> sp) \<noteq> 0) (stmt.Seq (translate_program C sp vp) (translate_program B sp vp))))
                                 (stmt.Havoc sp)"

fun get_deepest_operation_depth :: "trm \<Rightarrow> nat" where
"get_deepest_operation_depth (Op _ C1 C2) = 1 + max (get_deepest_operation_depth C1) (get_deepest_operation_depth C2)"|
"get_deepest_operation_depth (Seq C1 C2) = max (get_deepest_operation_depth C1) (get_deepest_operation_depth C2)"|
"get_deepest_operation_depth (Assign x C) = (get_deepest_operation_depth C)"|
"get_deepest_operation_depth (If B C1 C2) = max (max (get_deepest_operation_depth B) (get_deepest_operation_depth C1)) (get_deepest_operation_depth C2)"|
"get_deepest_operation_depth (While B C) = max (get_deepest_operation_depth B) (get_deepest_operation_depth C)"|
"get_deepest_operation_depth _ = 0"

definition program_translation :: "trm \<Rightarrow> (nat, val) stmt" where
"program_translation C = translate_program C 0 (1 + get_deepest_operation_depth C)"


definition transform_state_with_return_val :: "val \<Rightarrow> store \<Rightarrow> val list \<Rightarrow> nat \<Rightarrow> val npstate" where
"transform_state_with_return_val v \<sigma> l vp = (\<lambda>i. if i < length l then l ! i else (if i = length l then v else (if i < vp then 0 else \<sigma> (i - vp))))"

definition retval_state_translation where
"retval_state_translation v \<sigma> C = transform_state_with_return_val v \<sigma> [] (1 + get_deepest_operation_depth C)"

fun retval_state_translation_partial where 
"retval_state_translation_partial v \<sigma> None = transform_state_with_return_val v \<sigma> [] 1" |
"retval_state_translation_partial v \<sigma> (Some C) = retval_state_translation v \<sigma> C"



lemma stack_append: "length (prev_stack @ [v1]) < vp \<Longrightarrow> transform_state_with_return_val v1 \<sigma> prev_stack vp = transform_state_with_return_val 0 \<sigma> (prev_stack @ [v1]) vp"
  apply(rule ext)
  apply(auto simp add:transform_state_with_return_val_def)
   apply (simp add: nth_append_left)
  by (simp add: not_less_less_Suc_eq)


lemma subst_eq:
  assumes "y = y'"
  shows "\<sigma>(x := y) = \<sigma>(x:=y')"
  using assms by simp


lemma state_transform_subst:
  assumes "(length prev_stack) = sp \<and> (vp - sp) \<ge> 1+(get_deepest_operation_depth lhcC)"
  shows"(transform_state_with_return_val v0 \<sigma> prev_stack vp)(sp:=v) = (transform_state_with_return_val v \<sigma> prev_stack vp)"
  apply(rule ext)
  using assms by(auto simp add:transform_state_with_return_val_def)

lemma state_transform_subst_rev:
  assumes "(length prev_stack) = sp \<and> (vp - sp) \<ge> 1+(get_deepest_operation_depth lhcC)"
  and "transform_state_with_return_val v \<sigma> prev_stack vp = \<phi>(sp :=  v')"
shows "\<exists>v''. \<phi> = transform_state_with_return_val v'' \<sigma> prev_stack vp"
  apply(rule)
  apply(rule ext)
  using assms apply(auto simp add:transform_state_with_return_val_def)
proof-
  fix i
  assume "(\<lambda>i. if i < length prev_stack then prev_stack ! i else if i = length prev_stack then v else if i < vp then 0 else \<sigma> (i - vp)) = \<phi>(length prev_stack := v')"
  hence fct: "(if i < length prev_stack then prev_stack ! i else if i = length prev_stack then v else if i < vp then 0 else \<sigma> (i - vp)) = (\<phi>(length prev_stack := v')) i"
    by (smt (verit, best))
  assume asm: "i < length prev_stack"
  from fct asm show "\<phi> i = prev_stack ! i" by auto 
next
  fix i
  assume "(\<lambda>i. if i < length prev_stack then prev_stack ! i else if i = length prev_stack then v else if i < vp then 0 else \<sigma> (i - vp)) = \<phi>(length prev_stack := v')"
  hence fct: "(if i < length prev_stack then prev_stack ! i else if i = length prev_stack then v else if i < vp then 0 else \<sigma> (i - vp)) = (\<phi>(length prev_stack := v')) i"
    by (smt (verit, best))
  assume asm: "i < vp" and asm2: "i \<noteq> length prev_stack" and asm3: " \<not> i < length prev_stack"
  from fct asm asm2 asm3 show "\<phi> i = 0" by auto 
next
  fix i
  assume "(\<lambda>i. if i < length prev_stack then prev_stack ! i else if i = length prev_stack then v else if i < vp then 0 else \<sigma> (i - vp)) = \<phi>(length prev_stack := v')"
  hence fct: "(if i < length prev_stack then prev_stack ! i else if i = length prev_stack then v else if i < vp then 0 else \<sigma> (i - vp)) = (\<phi>(length prev_stack := v')) i"
    by (smt (verit, best))
  assume asm: "\<not> i < vp" and asm2: "i \<noteq> length prev_stack" and asm3: " \<not> i < length prev_stack"
  from fct asm asm2 asm3 show "\<phi> i = \<sigma> (i - vp)" by auto 
qed


lemma state_transform_eq:
  assumes "transform_state_with_return_val v \<sigma> prev_stack vp = transform_state_with_return_val v' \<sigma>' prev_stack vp"
  and "(length prev_stack) = sp \<and> (vp - sp) \<ge> 1"
  shows "v = v' \<and> \<sigma> = \<sigma>'" 
  apply(rule)
  using assms apply(auto simp add:transform_state_with_return_val_def)[1]
  apply (metis less_irrefl_nat)
proof
  fix i
  from assms have f: "transform_state_with_return_val v \<sigma> prev_stack vp (vp + i) = transform_state_with_return_val v' \<sigma>' prev_stack vp (vp + i)" 
    by auto
  from assms have "vp + i > length prev_stack" by auto
  with f show "\<sigma> i = \<sigma>' i"
    by(auto simp add:transform_state_with_return_val_def)
qed


lemma state_transform_var_acc:
  assumes "(length prev_stack) = sp \<and> (vp - sp) \<ge> 1+(get_deepest_operation_depth lhcC)"
  shows "(transform_state_with_return_val v0 \<sigma> prev_stack vp) (vp + x) = (\<sigma> x)"
  using assms by(auto simp add:transform_state_with_return_val_def)

lemma state_transform_sp_acc:
  assumes "(length prev_stack) = sp \<and> (vp - sp) \<ge> 1+(get_deepest_operation_depth lhcC)"
  shows "(transform_state_with_return_val v0 \<sigma> prev_stack vp) sp = v0"
  using assms by(auto simp add:transform_state_with_return_val_def)

lemma translated_program_step_state:
  assumes "\<langle>translate_program lhcC sp vp, transform_state_with_return_val v \<sigma> prev_stack vp\<rangle> \<rightarrow> \<phi>"
  and "(length prev_stack) = sp \<and> (vp - sp) \<ge> 1+(get_deepest_operation_depth lhcC)"
  shows "\<exists>v' \<sigma>'. \<phi> = transform_state_with_return_val v' \<sigma>' prev_stack vp"
  using assms
proof(induction lhcC arbitrary: v \<sigma> sp \<phi> prev_stack)
  case (Val x)
  hence "\<phi> = (transform_state_with_return_val v \<sigma> prev_stack vp)(sp:=x)" by auto
  moreover have "(transform_state_with_return_val v \<sigma> prev_stack vp)(sp:=x) = (transform_state_with_return_val x \<sigma> prev_stack vp)"
    apply(rule ext)
    using Val by(auto simp add:transform_state_with_return_val_def)
  ultimately show ?case by auto
next
  case (Var x)
  hence "\<phi> = (transform_state_with_return_val v \<sigma> prev_stack vp)(sp:= ((transform_state_with_return_val v \<sigma> prev_stack vp) (vp + x)))" by auto
  moreover have "(transform_state_with_return_val v \<sigma> prev_stack vp)(sp:= ((transform_state_with_return_val v \<sigma> prev_stack vp) (vp + x))) = (transform_state_with_return_val ((transform_state_with_return_val v \<sigma> prev_stack vp) (vp + x)) \<sigma> prev_stack vp)"
    apply(rule ext)
    using Var by(auto simp add:transform_state_with_return_val_def)
  ultimately show ?case by auto
next
  case Havoc
  from this obtain v' where "\<phi> = (transform_state_with_return_val v \<sigma> prev_stack vp)(sp:=v')" by auto
  moreover have "(transform_state_with_return_val v \<sigma> prev_stack vp)(sp:=v') = (transform_state_with_return_val v' \<sigma> prev_stack vp)"
    apply(rule ext)
    using Havoc by(auto simp add:transform_state_with_return_val_def)
  ultimately show ?case by auto
next
  case (Op op lhcC1 lhcC2)
  hence asm:"length prev_stack = sp \<and> 1 + get_deepest_operation_depth (Op op lhcC1 lhcC2) \<le> vp - sp" by auto
  from Op have opfct: "\<langle>translate_program (Op op lhcC1 lhcC2) sp vp, transform_state_with_return_val v \<sigma> prev_stack vp\<rangle> \<rightarrow> \<phi>" by auto
  from opfct obtain \<phi>' \<phi>'' \<phi>''' where c1fct: "\<langle>(translate_program lhcC1 sp vp),transform_state_with_return_val v \<sigma> prev_stack vp\<rangle> \<rightarrow> \<phi>'" 
                           and   c2fct: "\<langle>(translate_program lhcC2 (Suc sp) vp), \<phi>'\<rangle> \<rightarrow> \<phi>''"
                           and   assopfct: "\<langle>(stmt.Assign sp (\<lambda>\<sigma>. op (\<sigma> sp) (\<sigma> (Suc sp)))), \<phi>''\<rangle> \<rightarrow> \<phi>'''"
                           and   ass0fct: "\<langle>((stmt.Assign (Suc sp) (\<lambda>\<sigma>. 0))), \<phi>'''\<rangle> \<rightarrow> \<phi>"
    by (auto del:single_sem_Assign_elim)
  from c1fct Op obtain v' \<sigma>'  where phi'fct: "\<phi>' = transform_state_with_return_val v' \<sigma>' prev_stack vp" 
    by force
  from asm have stk_fct:"length (prev_stack @ [v']) = (Suc sp)" and dpth_fct:"1 + get_deepest_operation_depth lhcC2 \<le> vp - (Suc sp)" by auto
  from phi'fct stack_append stk_fct dpth_fct have "\<phi>' = transform_state_with_return_val 0 \<sigma>' (prev_stack @ [v']) vp" by auto
  with c2fct have "\<langle>(translate_program lhcC2 (Suc sp) vp), transform_state_with_return_val 0 \<sigma>' (prev_stack @ [v']) vp\<rangle> \<rightarrow> \<phi>''" by auto
  with Op obtain v'' \<sigma>''  where phi''fct: "\<phi>'' = transform_state_with_return_val v'' \<sigma>'' (prev_stack @ [v']) vp" 
    by force
  from assopfct have "\<phi>''' = \<phi>''(sp := op (\<phi>'' sp) (\<phi>'' (Suc sp)))" by auto
  moreover from phi''fct asm have "(\<phi>'' sp) = v'" by(auto simp add:transform_state_with_return_val_def)
  moreover from phi''fct stk_fct have "(\<phi>'' (Suc sp)) = v''" by(auto simp add:transform_state_with_return_val_def)
  moreover have "\<phi>''(sp := op v' v'') = transform_state_with_return_val v'' \<sigma>'' (prev_stack @ [op v' v'']) vp"
    apply (rule ext)
    using phi''fct asm
    apply(auto simp add:transform_state_with_return_val_def)
    by (simp add: nth_append)
  ultimately have phi'''fct: "\<phi>''' = transform_state_with_return_val v'' \<sigma>'' (prev_stack @ [op v' v'']) vp" by auto
  moreover from ass0fct have "\<phi> = \<phi>'''(Suc sp := 0)" by auto
  moreover have "(transform_state_with_return_val v'' \<sigma>'' (prev_stack @ [op v' v'']) vp)(Suc sp := 0) = (transform_state_with_return_val 0 \<sigma>'' (prev_stack @ [op v' v'']) vp)"
    apply(rule ext)
    using stk_fct by(auto simp add:transform_state_with_return_val_def)
  moreover from stack_append stk_fct dpth_fct have "(transform_state_with_return_val 0 \<sigma>'' (prev_stack @ [op v' v'']) vp) = (transform_state_with_return_val (op v' v'') \<sigma>'' prev_stack vp)" by auto
  ultimately show ?case by auto
next
  case (Assign x lhcC)
  from this obtain \<phi>' where cfct: "\<langle>translate_program lhcC sp vp, transform_state_with_return_val v \<sigma> prev_stack vp\<rangle> \<rightarrow> \<phi>'"
                      and "\<phi> = \<phi>'((vp + x) := \<phi>' sp)" 
    by auto
  moreover from Assign cfct obtain v' \<sigma>' where "\<phi>' = transform_state_with_return_val v' \<sigma>' prev_stack vp" by force
  moreover have "(transform_state_with_return_val v' \<sigma>' prev_stack vp)((vp + x):= ((transform_state_with_return_val v' \<sigma>' prev_stack vp) sp)) = (transform_state_with_return_val v' (\<sigma>'(x:=((transform_state_with_return_val v' \<sigma>' prev_stack vp) sp))) prev_stack vp)"
    apply(rule ext)
    using Assign by(auto simp add:transform_state_with_return_val_def)
  ultimately show ?case by auto
next
  case (Seq lhcC1 lhcC2)
  hence "\<langle>translate_program (lhcC1 ;; lhcC2) sp vp, transform_state_with_return_val v \<sigma> prev_stack vp\<rangle> \<rightarrow> \<phi>" by auto
  from this obtain \<phi>' \<phi>'' where cfct: "\<langle>translate_program lhcC1 sp vp, transform_state_with_return_val v \<sigma> prev_stack vp\<rangle> \<rightarrow> \<phi>'" 
                        and  cfct2: "\<langle>translate_program lhcC2 sp vp, \<phi>'\<rangle> \<rightarrow> \<phi>''"
                        and havocfct: "\<langle>stmt.Havoc sp, \<phi>''\<rangle> \<rightarrow> \<phi>"
    by(auto del:single_sem_Havoc_elim)
  from cfct Seq obtain v' \<sigma>' where phi'fct: "\<phi>' = transform_state_with_return_val v' \<sigma>' prev_stack vp" by force
  from phi'fct Seq cfct2 obtain v'' \<sigma>'' where phi''fct: "\<phi>'' = transform_state_with_return_val v'' \<sigma>'' prev_stack vp" by force
  from phi''fct havocfct obtain v''' where  "\<phi> = (transform_state_with_return_val v'' \<sigma>'' prev_stack vp)(sp:=v''')" by auto
  moreover have "(transform_state_with_return_val v'' \<sigma>'' prev_stack vp)(sp:=v''') = (transform_state_with_return_val v''' \<sigma>'' prev_stack vp)" 
    apply(rule ext)
    using Seq by (auto simp add:transform_state_with_return_val_def)
  ultimately show ?case by auto
next
  case (If B C1 C2)
  from this obtain \<phi>' where bfct: "\<langle>translate_program B sp vp, transform_state_with_return_val v \<sigma> prev_stack vp\<rangle> \<rightarrow> \<phi>'"
                        and iffct: "\<langle>(if_then_else (\<lambda>\<sigma>. (\<sigma> sp) \<noteq> 0) (translate_program C1 sp vp) (translate_program C2 sp vp)), \<phi>'\<rangle> \<rightarrow> \<phi>"
    by auto
  from If bfct obtain v' \<sigma>' where phi'fct: "\<phi>' = transform_state_with_return_val v' \<sigma>' prev_stack vp" by force
  from iffct have "\<langle>(translate_program C1 sp vp), \<phi>'\<rangle> \<rightarrow> \<phi> \<or> \<langle>(translate_program C2 sp vp), \<phi>'\<rangle> \<rightarrow> \<phi>" unfolding if_then_else_def
    by auto
  from this If phi'fct obtain v'' \<sigma>'' where "\<phi> = transform_state_with_return_val v'' \<sigma>'' prev_stack vp" by force
  then show ?case by auto
next
  case Skip
  hence asm: "length prev_stack = sp \<and> 1 + get_deepest_operation_depth trm.Skip \<le> vp - sp" by auto
  from Skip obtain va where "\<phi> = (transform_state_with_return_val v \<sigma> prev_stack vp)(sp := va)" by auto
  moreover have "(transform_state_with_return_val v \<sigma> prev_stack vp)(sp := va) = (transform_state_with_return_val va \<sigma> prev_stack vp)"
    apply(rule ext)
    using asm
    by(auto simp add:transform_state_with_return_val_def)
  ultimately show ?case by auto
next
  case (While B C)
  from While obtain \<phi>' \<phi>'' where Bfct: "\<langle>(translate_program B sp vp), transform_state_with_return_val v \<sigma> prev_stack vp \<rangle> \<rightarrow> \<phi>'"
                         and whilefct: "\<langle>(while_cond (\<lambda>\<sigma>. (\<sigma> sp) \<noteq> 0) (stmt.Seq (translate_program C sp vp) (translate_program B sp vp))), \<phi>'\<rangle> \<rightarrow> \<phi>''"
                           and havocfct: "\<langle>stmt.Havoc sp, \<phi>''\<rangle> \<rightarrow> \<phi>"
    by (auto del:single_sem_Havoc_elim)
  from While Bfct obtain v' \<sigma>' where phi'fct: "\<phi>' = transform_state_with_return_val v' \<sigma>' prev_stack vp"
    by force
  from whilefct have "\<langle>stmt.While (stmt.Assume (\<lambda>\<sigma>. (\<sigma> sp) \<noteq> 0);; (stmt.Seq (translate_program C sp vp) (translate_program B sp vp))), \<phi>'\<rangle> \<rightarrow> \<phi>''"
    unfolding while_cond_def
    by(auto)
  hence "\<exists>v'' \<sigma>''. \<phi>'' = transform_state_with_return_val v'' \<sigma>'' prev_stack vp" using phi'fct
  proof(induction "stmt.While (stmt.Assume (\<lambda>\<sigma>. (\<sigma> sp) \<noteq> 0);; (stmt.Seq (translate_program C sp vp) (translate_program B sp vp)))" \<phi>' \<phi>'' arbitrary: v' \<sigma>' rule:single_sem.induct)
    case (SemWhileIter \<sigma>'' \<sigma>''' \<sigma>'''')
    from SemWhileIter have sig''fct: "\<sigma>'' = transform_state_with_return_val v' \<sigma>' prev_stack vp" by auto
    from SemWhileIter have "\<langle>Assume (\<lambda>\<sigma>. \<sigma> sp \<noteq> 0) ;; (translate_program C sp vp ;; translate_program B sp vp), \<sigma>''\<rangle> \<rightarrow> \<sigma>'''" by auto
    from this obtain \<phi>''' where cfct: "\<langle>(translate_program C sp vp), \<sigma>''\<rangle> \<rightarrow> \<phi>'''"
                            and bfct: "\<langle>(translate_program B sp vp),  \<phi>'''\<rangle> \<rightarrow> \<sigma>'''"
      by auto
    from sig''fct cfct While obtain \<gamma> u where  phi'''fct: "\<phi>''' = transform_state_with_return_val u \<gamma> prev_stack vp"
      by force
    from phi'''fct bfct While obtain \<gamma>' u' where  "\<sigma>''' = transform_state_with_return_val u' \<gamma>' prev_stack vp"
      by force
    with SemWhileIter show ?case by blast
  next
    case (SemWhileExit \<sigma>)
    then show ?case by auto
  qed
  from this obtain v'' \<sigma>'' where "\<phi>'' = transform_state_with_return_val v'' \<sigma>'' prev_stack vp" by force
  with havocfct obtain v''' where "\<phi> = (transform_state_with_return_val v'' \<sigma>'' prev_stack vp)(sp :=  v''')" by auto
  moreover have "(transform_state_with_return_val v'' \<sigma>'' prev_stack vp)(sp :=  v''') = (transform_state_with_return_val v''' \<sigma>'' prev_stack vp)"
    apply(rule ext)
    using While by(auto simp add:transform_state_with_return_val_def) 
  ultimately show ?case by auto
qed



lemma LHC_RHHL_sem_equiv_general: "(length prev_stack) = sp \<and> (vp - sp) \<ge> 1+(get_deepest_operation_depth lhcC) \<Longrightarrow> (\<langle>lhcC, \<sigma>\<rangle> \<Down> \<langle>v, \<sigma>'\<rangle> = (\<langle>translate_program lhcC sp vp, transform_state_with_return_val v0 \<sigma> prev_stack vp\<rangle> \<rightarrow> (transform_state_with_return_val v \<sigma>' prev_stack vp)))"
proof
  assume asm: "length prev_stack = sp \<and> 1 + get_deepest_operation_depth lhcC \<le> vp - sp"
  assume "\<langle>lhcC, \<sigma>\<rangle> \<Down> \<langle>v, \<sigma>'\<rangle>"
  thus "\<langle>translate_program lhcC sp
          vp, transform_state_with_return_val v0 \<sigma> prev_stack vp\<rangle> \<rightarrow> transform_state_with_return_val v \<sigma>' prev_stack vp" using asm
  proof(induction arbitrary: prev_stack sp v0 rule:big_sem.induct)
    case (SemSkip \<sigma> v)
    show ?case
      apply(auto)
      apply(rule single_sem_eq_fin)
       apply(rule single_sem.SemHavoc[where ?v="v"])
      apply(rule ext)
      using SemSkip
      by(auto simp add:transform_state_with_return_val_def)
  next
    case (SemAssign C \<sigma> v \<sigma>' x)
    hence fct: "\<langle>translate_program C sp vp, transform_state_with_return_val v0 \<sigma> prev_stack vp\<rangle> \<rightarrow> transform_state_with_return_val v \<sigma>' prev_stack vp" by auto
    have "\<langle>stmt.Seq (translate_program C sp vp) (stmt.Assign (vp + x) (\<lambda>\<sigma>. (\<sigma> sp)))
      , transform_state_with_return_val v0 \<sigma> prev_stack vp\<rangle> \<rightarrow> (transform_state_with_return_val v \<sigma>' prev_stack vp)((vp + x):=(transform_state_with_return_val v \<sigma>' prev_stack vp) sp)" 
      apply(rule single_sem.SemSeq[where ?\<sigma>1.0="transform_state_with_return_val v \<sigma>' prev_stack vp"])
       apply(simp add:fct)
      apply(rule single_sem.SemAssign)
      done
    moreover from SemAssign have "(transform_state_with_return_val v \<sigma>' prev_stack vp) sp = v" by(auto simp add:transform_state_with_return_val_def)
    moreover have "transform_state_with_return_val v (\<sigma>'(x := v)) prev_stack vp = (transform_state_with_return_val v \<sigma>' prev_stack vp)((vp + x):=v)"
      apply(rule ext)
      apply(auto simp add:transform_state_with_return_val_def)
      using SemAssign
      by auto
    ultimately show ?case 
      by (metis translate_program.simps(7))
  next
    case (SemSeq C1 \<sigma> v1 \<sigma>' C2 v2 \<sigma>'' v)
    assume asm: "length prev_stack = sp \<and> 1 + get_deepest_operation_depth (C1 ;; C2) \<le> vp - sp"
    from SemSeq have fctC1: "\<langle>translate_program C1 sp
      vp, transform_state_with_return_val v0 \<sigma> prev_stack vp\<rangle> \<rightarrow> transform_state_with_return_val v1 \<sigma>' prev_stack vp" by auto
    from SemSeq have fctC2: "\<langle>translate_program C2 sp
      vp, transform_state_with_return_val v1 \<sigma>' prev_stack vp\<rangle> \<rightarrow> transform_state_with_return_val v2 \<sigma>'' prev_stack vp" by auto
    show ?case 
      apply(auto)
      apply(rule single_sem.SemSeq[where ?\<sigma>1.0="transform_state_with_return_val v2 \<sigma>'' prev_stack vp"])
      apply(rule)
      using fctC1
       apply(simp)
      using fctC2 
       apply(simp)
      apply(rule single_sem_eq_fin)
       apply(rule single_sem.SemHavoc[where ?v = "v"])
      apply(rule ext)
      apply(auto simp add:asm transform_state_with_return_val_def)
      done
  next
    case (SemIfTrue B \<sigma> vb \<sigma>' C1 v \<sigma>'' C2)
    assume vbtrue: "vb \<noteq> 0"
    assume asm:"length prev_stack = sp \<and> 1 + get_deepest_operation_depth (trm.If B C1 C2) \<le> vp - sp"
    from SemIfTrue have fctB:"\<langle>translate_program B sp
      vp, transform_state_with_return_val v0 \<sigma> prev_stack vp\<rangle> \<rightarrow> transform_state_with_return_val vb \<sigma>' prev_stack vp" by auto
    from SemIfTrue have fctC: "\<langle>translate_program C1 sp
      vp, transform_state_with_return_val vb \<sigma>' prev_stack vp\<rangle> \<rightarrow> transform_state_with_return_val v \<sigma>'' prev_stack vp" by auto
    show ?case 
      apply(auto)
      apply(rule single_sem.SemSeq)
      using fctB
       apply(simp)
      unfolding if_then_else_def
      apply(rule single_sem.SemIf1)
      apply(rule single_sem.SemSeq)
       apply(rule single_sem.SemAssume)
      using asm vbtrue
       apply(auto simp add:transform_state_with_return_val_def)[1]
      using fctC
      apply auto
      done
  next
    case (SemIfFalse B \<sigma> vb \<sigma>' C2 v \<sigma>'' C1)
    assume vbfalse: "vb = 0"
    assume asm:"length prev_stack = sp \<and> 1 + get_deepest_operation_depth (trm.If B C1 C2) \<le> vp - sp"
    from SemIfFalse have fctB:"\<langle>translate_program B sp
      vp, transform_state_with_return_val v0 \<sigma> prev_stack vp\<rangle> \<rightarrow> transform_state_with_return_val vb \<sigma>' prev_stack vp" by auto
    from SemIfFalse have fctC: "\<langle>translate_program C2 sp
      vp, transform_state_with_return_val vb \<sigma>' prev_stack vp\<rangle> \<rightarrow> transform_state_with_return_val v \<sigma>'' prev_stack vp" by auto
    show ?case 
      apply(auto)
      apply(rule single_sem.SemSeq)
      using fctB
       apply(simp)
      unfolding if_then_else_def
      apply(rule single_sem.SemIf2)
      apply(rule single_sem.SemSeq)
       apply(rule single_sem.SemAssume)
      unfolding lnot_def using asm vbfalse
       apply(auto simp add:transform_state_with_return_val_def)[1]
      using fctC
      apply auto
      done
  next
    case (SemWhileTrue B \<sigma> vb \<sigma>' C v \<sigma>'' v' \<sigma>''')
    assume vbtrue: "vb \<noteq> 0"
    assume asm: "length prev_stack = sp \<and> 1 + get_deepest_operation_depth (trm.While B C) \<le> vp - sp"
    from SemWhileTrue have fctB:"\<langle>translate_program B sp
      vp, transform_state_with_return_val v0 \<sigma> prev_stack vp\<rangle> \<rightarrow> transform_state_with_return_val vb \<sigma>' prev_stack vp" by auto
    from SemWhileTrue have fctC: "\<langle>translate_program C sp
      vp, transform_state_with_return_val vb \<sigma>' prev_stack vp\<rangle> \<rightarrow> transform_state_with_return_val v \<sigma>'' prev_stack vp" by auto
    from SemWhileTrue have " \<langle>translate_program (trm.While B C) sp
      vp, transform_state_with_return_val v \<sigma>'' prev_stack vp\<rangle> \<rightarrow> transform_state_with_return_val v' \<sigma>''' prev_stack vp" by auto
    hence "\<exists>\<phi> \<phi>' \<phi>''. \<langle>translate_program B sp vp, transform_state_with_return_val v \<sigma>'' prev_stack vp\<rangle> \<rightarrow> \<phi> \<and> 
                   \<langle>stmt.While (Assume (\<lambda>\<sigma>. \<sigma> sp \<noteq> 0) ;; (translate_program C sp vp ;; translate_program B sp vp)), \<phi>\<rangle> \<rightarrow> \<phi>' \<and>
                   \<langle>Assume (lnot (\<lambda>\<sigma>. \<sigma> sp \<noteq> 0)), \<phi>'\<rangle> \<rightarrow> \<phi>'' \<and>
                   \<langle>stmt.Havoc sp, \<phi>''\<rangle> \<rightarrow> transform_state_with_return_val v' \<sigma>''' prev_stack vp"
      by (auto simp add:while_cond_def del:single_sem_Assume_elim single_sem_Havoc_elim)
    from this obtain \<phi> \<phi>' \<phi>'' where fctB2: "\<langle>translate_program B sp vp, transform_state_with_return_val v \<sigma>'' prev_stack vp\<rangle> \<rightarrow> \<phi>" and 
                   fctWhile: "\<langle>stmt.While (Assume (\<lambda>\<sigma>. \<sigma> sp \<noteq> 0) ;; (translate_program C sp vp ;; translate_program B sp vp)), \<phi>\<rangle> \<rightarrow> \<phi>'" and
                   fctAssm:"\<langle>Assume (lnot (\<lambda>\<sigma>. \<sigma> sp \<noteq> 0)), \<phi>'\<rangle> \<rightarrow> \<phi>''" and
                   fctHavoc:"\<langle>stmt.Havoc sp, \<phi>''\<rangle> \<rightarrow> transform_state_with_return_val v' \<sigma>''' prev_stack vp" by meson
    show ?case 
      apply(auto)
      apply(rule single_sem.SemSeq)
      apply(rule single_sem.SemSeq)
      using fctB
       apply(simp)
      unfolding while_cond_def
       apply(rule single_sem.SemSeq)  
        apply(rule single_sem.SemWhileIter)
         apply(rule single_sem.SemSeq)
          apply(rule single_sem.SemAssume)
        using vbtrue asm
            apply(simp add:transform_state_with_return_val_def)
        apply(rule single_sem.SemSeq)
        using fctC apply(simp)
        using fctB2 apply(simp)
        using fctWhile apply(simp)
        using fctAssm apply(simp)
        using fctHavoc apply(simp)
        done
  next
    case (SemWhileFalse B \<sigma> vb \<sigma>' C v)
    assume vbfalse: "vb = 0"
    assume asm: "length prev_stack = sp \<and> 1 + get_deepest_operation_depth (trm.While B C) \<le> vp - sp"
    from SemWhileFalse have fctB:"\<langle>translate_program B sp
      vp, transform_state_with_return_val v0 \<sigma> prev_stack vp\<rangle> \<rightarrow> transform_state_with_return_val vb \<sigma>' prev_stack vp" by auto
    show ?case 
      apply(auto)
      apply(rule single_sem.SemSeq)
      apply(rule single_sem.SemSeq)
      using fctB
       apply(simp)
      unfolding while_cond_def
      apply(rule single_sem.SemSeq)
       apply(rule single_sem.SemWhileExit)
       apply(rule single_sem.SemAssume)
      unfolding lnot_def using vbfalse asm
       apply(simp add:transform_state_with_return_val_def)
      apply(rule single_sem_eq_fin)
       apply(rule single_sem.SemHavoc[where ?v="v"])
      apply(rule ext)
      using asm
      apply(auto simp add:transform_state_with_return_val_def)
      done
  next
    case (SemVal v \<sigma>)
    show ?case
      apply(auto)
      apply(rule single_sem_eq_fin)
       apply(rule single_sem.SemAssign)
      apply(rule ext)
      using SemVal
      by(auto simp add:transform_state_with_return_val_def)
  next
    case (SemVar x \<sigma>)
    show ?case 
      apply(auto)
      apply(rule single_sem_eq_fin)
       apply(rule single_sem.SemAssign)
      apply(rule ext)
      using SemVar
      by(auto simp add:transform_state_with_return_val_def)
  next
    case (SemHavoc \<sigma> v)
    show ?case 
      apply(auto)
      apply(rule single_sem_eq_fin)
       apply(rule single_sem.SemHavoc[where ?v="v"])
      apply(rule ext)
      using SemHavoc
      by(auto simp add:transform_state_with_return_val_def)
  next
    case (SemOp C1 \<sigma> v1 \<sigma>' C2 v2 \<sigma>'' op)
    with asm have fct: "\<langle>translate_program C1 sp vp, transform_state_with_return_val v0 \<sigma> prev_stack vp\<rangle> \<rightarrow> transform_state_with_return_val v1 \<sigma>' prev_stack vp" by auto
    let ?sp = "Suc sp" and ?prev_stack = "prev_stack @ [v1]"
    assume "length prev_stack = sp \<and> 1 + get_deepest_operation_depth (Op op C1 C2) \<le> vp - sp"
    hence stk_fct:"length ?prev_stack = ?sp" and dpth_fct:"1 + get_deepest_operation_depth C2 \<le> vp - ?sp" by auto
    with SemOp have fct2: "\<langle>translate_program C2 ?sp
      vp, transform_state_with_return_val 0 \<sigma>' ?prev_stack vp\<rangle> \<rightarrow> transform_state_with_return_val v2 \<sigma>'' ?prev_stack vp" by blast
    show ?case
      apply(auto)
      apply(rule single_sem.SemSeq[where ?\<sigma>1.0 = "transform_state_with_return_val v1 \<sigma>' prev_stack vp"])
       apply(auto simp add:fct)
      apply(rule single_sem.SemSeq[where ?\<sigma>1.0="transform_state_with_return_val v2 \<sigma>'' ?prev_stack vp"])
      using stack_append dpth_fct stk_fct fct2 apply auto[1]
      apply(rule single_sem.SemSeq)
       apply(rule single_sem_eq_fin[where ?\<sigma>'.0="transform_state_with_return_val v2 \<sigma>'' (prev_stack @ [op v1 v2]) vp"])
        apply(rule single_sem.SemAssign)
       apply(rule trans[where ?s="(transform_state_with_return_val v2 \<sigma>'' (prev_stack @ [v1]) vp) (sp := op v1 v2)"])
        apply(rule subst_eq)
        apply(rule HOL.arg_cong2[where ?b="v1" and ?d="v2"])
      using stk_fct
         apply(auto simp add:transform_state_with_return_val_def stk_fct)[1]
      using stk_fct
        apply(auto simp add:transform_state_with_return_val_def)[1]
       apply(rule ext)
      using stk_fct
       apply (auto simp add:transform_state_with_return_val_def)[1]
       apply (simp add: nth_append_left)
      apply(rule single_sem_eq_fin)
       apply(rule single_sem.SemAssign)
      apply(rule ext)
      using stk_fct dpth_fct
      apply (auto simp add:transform_state_with_return_val_def)[1]
      apply (simp add: nth_append_left)
      done
  qed
next
  assume "\<langle>translate_program lhcC sp
       vp, transform_state_with_return_val v0 \<sigma> prev_stack vp\<rangle> \<rightarrow> transform_state_with_return_val v \<sigma>' prev_stack vp"
  thus "length prev_stack = sp \<and> (1 + get_deepest_operation_depth lhcC) \<le> vp - sp \<Longrightarrow> \<langle>lhcC, \<sigma>\<rangle> \<Down> \<langle>v, \<sigma>'\<rangle>"
  proof (induction lhcC arbitrary: prev_stack sp v0 \<sigma> v \<sigma>')
    case (Val x)
    hence "transform_state_with_return_val v \<sigma>' prev_stack vp = (transform_state_with_return_val v0 \<sigma> prev_stack vp)(sp:=x)" by auto
    with Val state_transform_subst have "transform_state_with_return_val v \<sigma>' prev_stack vp = (transform_state_with_return_val x \<sigma> prev_stack vp)"
      by metis
    with Val state_transform_eq have "v = x \<and> \<sigma>' = \<sigma>"
      using add_leD1 by blast
    then show ?case by (auto simp add:SemVal)
  next
    case (Var x)
    hence "transform_state_with_return_val v \<sigma>' prev_stack vp = (transform_state_with_return_val v0 \<sigma> prev_stack vp)(sp:=((transform_state_with_return_val v0 \<sigma> prev_stack vp) (vp + x)))"
      by(auto)
    with Var state_transform_subst have "transform_state_with_return_val v \<sigma>' prev_stack vp = (transform_state_with_return_val ((transform_state_with_return_val v0 \<sigma> prev_stack vp) (vp + x)) \<sigma> prev_stack vp)"
      by metis
    with Var state_transform_eq have f2: "v = ((transform_state_with_return_val v0 \<sigma> prev_stack vp) (vp + x)) \<and> \<sigma>' = \<sigma>" using add_leD1  by blast
    hence "\<sigma>' = \<sigma>" by auto
    from f2 Var state_transform_var_acc have "v = \<sigma> x" by blast
    from \<open>v = \<sigma> x\<close> \<open>\<sigma>' = \<sigma>\<close> show ?case by (auto simp add:SemVar) 
  next
    case Havoc
    from this obtain v' where "transform_state_with_return_val v \<sigma>' prev_stack vp = (transform_state_with_return_val v0 \<sigma> prev_stack vp)(sp := v')" by auto 
    with Havoc state_transform_subst have "transform_state_with_return_val v \<sigma>' prev_stack vp = (transform_state_with_return_val v' \<sigma> prev_stack vp)"
      by metis
    with Havoc state_transform_eq have "v = v' \<and> \<sigma> = \<sigma>'"
      using add_leD1 by blast
    then show ?case by (auto simp add:SemHavoc)
  next
    case (Op op lhcC1 lhcC2)
    hence asm:"length prev_stack = sp \<and> 1 + get_deepest_operation_depth (Op op lhcC1 lhcC2) \<le> vp - sp" by auto
    hence asmc1: "length prev_stack = sp \<and> 1 + get_deepest_operation_depth lhcC1 \<le> vp - sp" by auto
    from Op have opfct: "\<langle>translate_program (Op op lhcC1 lhcC2) sp vp, transform_state_with_return_val v0 \<sigma> prev_stack vp\<rangle> \<rightarrow> transform_state_with_return_val v \<sigma>' prev_stack vp" by auto
    from opfct obtain \<phi>' \<phi>'' \<phi>''' where c1fct: "\<langle>(translate_program lhcC1 sp vp),transform_state_with_return_val v0 \<sigma> prev_stack vp\<rangle> \<rightarrow> \<phi>'" 
                             and   c2fct: "\<langle>(translate_program lhcC2 (Suc sp) vp), \<phi>'\<rangle> \<rightarrow> \<phi>''"
                             and   assopfct: "\<langle>(stmt.Assign sp (\<lambda>\<sigma>. op (\<sigma> sp) (\<sigma> (Suc sp)))), \<phi>''\<rangle> \<rightarrow> \<phi>'''"
                             and   ass0fct: "\<langle>((stmt.Assign (Suc sp) (\<lambda>\<sigma>. 0))), \<phi>'''\<rangle> \<rightarrow> transform_state_with_return_val v \<sigma>' prev_stack vp"
      by (auto del:single_sem_Assign_elim)
    from c1fct Op translated_program_step_state obtain v' \<gamma>'  where phi'fct: "\<phi>' = transform_state_with_return_val v' \<gamma>' prev_stack vp" 
      by force
    from asm have stk_fct:"length (prev_stack @ [v']) = (Suc sp)" and dpth_fct:"1 + get_deepest_operation_depth lhcC2 \<le> vp - (Suc sp)" by auto
    from phi'fct stack_append stk_fct dpth_fct have "\<phi>' = transform_state_with_return_val 0 \<gamma>' (prev_stack @ [v']) vp" by auto
    with c2fct have c2fct':"\<langle>(translate_program lhcC2 (Suc sp) vp), transform_state_with_return_val 0 \<gamma>' (prev_stack @ [v']) vp\<rangle> \<rightarrow> \<phi>''" by auto
    with Op translated_program_step_state obtain v'' \<sigma>''  where phi''fct: "\<phi>'' = transform_state_with_return_val v'' \<sigma>'' (prev_stack @ [v']) vp" 
      by force
    from c1fct phi'fct Op asmc1 have stp1:"\<langle>lhcC1, \<sigma>\<rangle> \<Down> \<langle>v', \<gamma>'\<rangle>" by auto
    from phi''fct Op stk_fct dpth_fct c2fct' have stp2:"\<langle>lhcC2, \<gamma>'\<rangle> \<Down> \<langle>v'', \<sigma>''\<rangle>" 
      by (metis)
    from assopfct have "\<phi>''' = \<phi>''(sp := op (\<phi>'' sp) (\<phi>'' (Suc sp)))" by auto
    moreover from phi''fct asm have "(\<phi>'' sp) = v'" by(auto simp add:transform_state_with_return_val_def)
    moreover from phi''fct stk_fct have "(\<phi>'' (Suc sp)) = v''" by(auto simp add:transform_state_with_return_val_def)
    moreover  have "\<phi>''(sp := op v' v'') = transform_state_with_return_val v'' \<sigma>'' (prev_stack @ [op v' v'']) vp"
      apply (rule ext)
      using phi''fct asm
      apply(auto simp add:transform_state_with_return_val_def)
      by (simp add: nth_append)
    ultimately have phi'''fct: "\<phi>''' = transform_state_with_return_val v'' \<sigma>'' (prev_stack @ [op v' v'']) vp" by auto
    moreover from ass0fct have "transform_state_with_return_val v \<sigma>' prev_stack vp = \<phi>'''(Suc sp := 0)" by auto
    moreover have "(transform_state_with_return_val v'' \<sigma>'' (prev_stack @ [op v' v'']) vp)(Suc sp := 0) = (transform_state_with_return_val 0 \<sigma>'' (prev_stack @ [op v' v'']) vp)"
      apply(rule ext)
      using stk_fct by(auto simp add:transform_state_with_return_val_def)
    moreover from stack_append stk_fct dpth_fct have "(transform_state_with_return_val 0 \<sigma>'' (prev_stack @ [op v' v'']) vp) = (transform_state_with_return_val (op v' v'') \<sigma>'' prev_stack vp)" by auto
    ultimately have "transform_state_with_return_val v \<sigma>' prev_stack vp = (transform_state_with_return_val (op v' v'') \<sigma>'' prev_stack vp)" by auto
    with asm state_transform_eq have "v = (op v' v'') \<and> \<sigma>' = \<sigma>''" using add_leD1 by blast
    with stp1 stp2 show ?case by(auto simp add: SemOp)
  next
    case (Assign x lhcC)
    from this obtain \<phi>' where cfct: "\<langle>translate_program lhcC sp vp, transform_state_with_return_val v0 \<sigma> prev_stack vp\<rangle> \<rightarrow> \<phi>'"
                      and "transform_state_with_return_val v \<sigma>' prev_stack vp = \<phi>'((vp + x) := \<phi>' sp)" 
    by auto
    moreover from Assign cfct translated_program_step_state obtain v' \<gamma>' where phi'fct: "\<phi>' = transform_state_with_return_val v' \<gamma>' prev_stack vp" by force
    moreover have "(transform_state_with_return_val v' \<gamma>' prev_stack vp)((vp + x):= ((transform_state_with_return_val v' \<gamma>' prev_stack vp) sp)) = (transform_state_with_return_val v' (\<gamma>'(x:=((transform_state_with_return_val v' \<sigma>' prev_stack vp) sp))) prev_stack vp)"
      apply(rule ext)
      using Assign by(auto simp add:transform_state_with_return_val_def)
    ultimately have "v' = v \<and> \<sigma>' = (\<gamma>'(x:=((transform_state_with_return_val v' \<sigma>' prev_stack vp) sp)))"
      using Assign state_transform_eq using add_leD1 by metis
    moreover from phi'fct Assign cfct have "\<langle>lhcC, \<sigma>\<rangle> \<Down> \<langle>v', \<gamma>'\<rangle>" by auto
    moreover from state_transform_sp_acc Assign have "(transform_state_with_return_val v' \<sigma>' prev_stack vp) sp = v'" by blast
    ultimately show ?case
      by (metis big_sem.SemAssign)
  next
    case (Seq lhcC1 lhcC2 prev_stack sp v0 \<sigma> v \<sigma>''')
    from Seq have c1asm: "length prev_stack = sp \<and> 1 + get_deepest_operation_depth lhcC1 \<le> vp - sp" by auto
    from Seq have c2asm: "length prev_stack = sp \<and> 1 + get_deepest_operation_depth lhcC2 \<le> vp - sp" by auto
    from Seq translated_program_step_state obtain \<phi> \<phi>' where cfct: "\<langle>translate_program lhcC1 sp vp, transform_state_with_return_val v0 \<sigma> prev_stack vp\<rangle> \<rightarrow> \<phi>"
                                                      and c2fct: "\<langle>translate_program lhcC2 sp vp, \<phi>\<rangle> \<rightarrow> \<phi>'"
                                                      and havocfct: "\<langle>stmt.Havoc sp, \<phi>'\<rangle> \<rightarrow> transform_state_with_return_val v \<sigma>''' prev_stack vp"
      by (auto del: single_sem_Havoc_elim)
    moreover from cfct Seq translated_program_step_state obtain v' \<sigma>' where phifct: "\<phi> = transform_state_with_return_val v' \<sigma>' prev_stack vp"                                                             
      by force
    ultimately have stp1: "\<langle>lhcC1, \<sigma>\<rangle> \<Down> \<langle>v', \<sigma>'\<rangle>" using c1asm Seq by auto
    from phifct c2fct Seq translated_program_step_state obtain v'' \<sigma>'' where phi'fct: "\<phi>' = transform_state_with_return_val v'' \<sigma>'' prev_stack vp"                                                             
      by force
    from c2fct phifct phi'fct Seq c2asm have stp2: "\<langle>lhcC2, \<sigma>'\<rangle> \<Down> \<langle>v'', \<sigma>''\<rangle>" using c1asm Seq by auto
    from phi'fct havocfct obtain v''' where "transform_state_with_return_val v \<sigma>''' prev_stack vp = (transform_state_with_return_val v'' \<sigma>'' prev_stack vp)(sp:=v''')"
      by auto
    moreover have "(transform_state_with_return_val v'' \<sigma>'' prev_stack vp)(sp:=v''') = (transform_state_with_return_val v''' \<sigma>'' prev_stack vp)"
      apply(rule ext)
      using Seq by (auto simp add:transform_state_with_return_val_def)
    ultimately have "transform_state_with_return_val v \<sigma>''' prev_stack vp =transform_state_with_return_val v''' \<sigma>'' prev_stack vp" by auto
    hence "\<And>i. \<sigma>''' i = \<sigma>'' i" 
    proof -
      fix i
      assume "transform_state_with_return_val v \<sigma>''' prev_stack vp = transform_state_with_return_val v''' \<sigma>'' prev_stack vp"
      hence fct: "transform_state_with_return_val v \<sigma>''' prev_stack vp (vp + i) = transform_state_with_return_val v''' \<sigma>'' prev_stack vp  (vp + i)" by auto
      from Seq have "vp + i > length prev_stack" by auto
      with fct show "\<sigma>''' i = \<sigma>'' i" by(auto simp add:transform_state_with_return_val_def)
    qed
    hence "\<sigma>''' = \<sigma>''" by auto
    with stp1 stp2 show ?case
      by (simp add: big_sem.SemSeq)
  next
    case (If B C1 C2)
    from If have basm: "length prev_stack = sp \<and> 1 + get_deepest_operation_depth B \<le> vp - sp" by auto
    from If have c1asm: "length prev_stack = sp \<and> 1 + get_deepest_operation_depth C1 \<le> vp - sp" by auto
    from If have c2asm: "length prev_stack = sp \<and> 1 + get_deepest_operation_depth C2 \<le> vp - sp" by auto
    from If obtain \<phi>' where bfct: "\<langle>translate_program B sp vp, transform_state_with_return_val v0 \<sigma> prev_stack vp\<rangle> \<rightarrow> \<phi>'"
                          and iffct: "\<langle>(if_then_else (\<lambda>\<sigma>. (\<sigma> sp) \<noteq> 0) (translate_program C1 sp vp) (translate_program C2 sp vp)), \<phi>'\<rangle> \<rightarrow> transform_state_with_return_val v \<sigma>' prev_stack vp"
      by auto
    from If translated_program_step_state bfct obtain v' \<gamma>' where phi'fct: "\<phi>' = transform_state_with_return_val v' \<gamma>' prev_stack vp" 
      by force
    from phi'fct bfct If basm have bstep: "\<langle>B, \<sigma>\<rangle> \<Down> \<langle>v', \<gamma>'\<rangle>" by auto
    from phi'fct If state_transform_sp_acc have "\<phi>' sp = v'" by metis
    from this iffct have "v' \<noteq> 0 \<and> \<langle>(translate_program C1 sp vp), \<phi>'\<rangle> \<rightarrow> transform_state_with_return_val v \<sigma>' prev_stack vp \<or> v' = 0 \<and> \<langle>(translate_program C2 sp vp), \<phi>'\<rangle> \<rightarrow> transform_state_with_return_val v \<sigma>' prev_stack vp" unfolding if_then_else_def lnot_def
      by auto
    then show ?case
    proof
      assume "v' \<noteq> 0 \<and> \<langle>translate_program C1 sp vp, \<phi>'\<rangle> \<rightarrow> transform_state_with_return_val v \<sigma>' prev_stack vp"
      hence c1fct: "\<langle>translate_program C1 sp vp, \<phi>'\<rangle> \<rightarrow> transform_state_with_return_val v \<sigma>' prev_stack vp" and "v' \<noteq> 0" by auto
      from phi'fct c1fct If c1asm have "\<langle>C1, \<gamma>'\<rangle> \<Down> \<langle>v, \<sigma>'\<rangle>" by metis
      from this \<open>v' \<noteq> 0\<close> bstep show "\<langle>trm.If B C1 C2, \<sigma>\<rangle> \<Down> \<langle>v, \<sigma>'\<rangle>" by (auto simp add:SemIfTrue)
    next
      assume "v' = 0 \<and> \<langle>translate_program C2 sp vp, \<phi>'\<rangle> \<rightarrow> transform_state_with_return_val v \<sigma>' prev_stack vp"
      hence c2fct: "\<langle>translate_program C2 sp vp, \<phi>'\<rangle> \<rightarrow> transform_state_with_return_val v \<sigma>' prev_stack vp" and "v' = 0" by auto
      from phi'fct c2fct If c2asm have "\<langle>C2, \<gamma>'\<rangle> \<Down> \<langle>v, \<sigma>'\<rangle>" by metis
      from this \<open>v' = 0\<close> bstep show "\<langle>trm.If B C1 C2, \<sigma>\<rangle> \<Down> \<langle>v, \<sigma>'\<rangle>" by (auto simp add:SemIfFalse)
    qed
  next
    case Skip
    hence asm: "length prev_stack = sp \<and> 1 + get_deepest_operation_depth trm.Skip \<le> vp - sp" by auto
    from Skip have "\<langle>stmt.Havoc sp, transform_state_with_return_val v0 \<sigma> prev_stack vp\<rangle> \<rightarrow> transform_state_with_return_val v \<sigma>' prev_stack vp" by auto 
    hence "\<And>i. \<sigma>' i = \<sigma> i"
    proof (cases)
      fix i
      case (SemHavoc v)
      from asm have asm_fct: "i + vp > length prev_stack" by auto
      from SemHavoc have "transform_state_with_return_val v \<sigma>' prev_stack vp (i+vp) = ((transform_state_with_return_val v0 \<sigma> prev_stack vp)(sp := v)) (i+vp)"
        by (metis fun_upd_apply less_irrefl_nat asm transform_state_with_return_val_def)
      thus "\<sigma>' i = \<sigma> i"
        using asm_fct asm
        by(auto simp add:transform_state_with_return_val_def)
    qed
    then show ?case
      by (simp add: big_sem.SemSkip)
  next
    case (While B C)
    from While have asm: "length prev_stack = sp \<and> 1 + get_deepest_operation_depth (trm.While B C) \<le> vp - sp" by auto
    from While have basm: "length prev_stack = sp \<and> 1 + get_deepest_operation_depth B \<le> vp - sp" by auto
    from While have casm: "length prev_stack = sp \<and> 1 + get_deepest_operation_depth C \<le> vp - sp" by auto
    from While obtain \<phi>' \<phi>'' where Bfct: "\<langle>(translate_program B sp vp), transform_state_with_return_val v0 \<sigma> prev_stack vp \<rangle> \<rightarrow> \<phi>'"
                           and whilefct: "\<langle>(while_cond (\<lambda>\<sigma>. (\<sigma> sp) \<noteq> 0) (stmt.Seq (translate_program C sp vp) (translate_program B sp vp))), \<phi>'\<rangle> \<rightarrow> \<phi>''"
                             and havocfct: "\<langle>stmt.Havoc sp, \<phi>''\<rangle> \<rightarrow> transform_state_with_return_val v \<sigma>' prev_stack vp"
      by (auto del:single_sem_Havoc_elim)
    from While Bfct translated_program_step_state obtain v' \<sigma>'' where phi'fct: "\<phi>' = transform_state_with_return_val v' \<sigma>'' prev_stack vp"
      by force
    with havocfct obtain v'''' where phi''fct: "transform_state_with_return_val v \<sigma>' prev_stack vp = \<phi>''(sp :=  v'''')" by auto
    from this state_transform_subst_rev asm obtain v''' where phi''fct:"\<phi>'' = transform_state_with_return_val v''' \<sigma>' prev_stack vp" by blast
    from whilefct obtain \<phi>''' where while_only:"\<langle>stmt.While (stmt.Assume (\<lambda>\<sigma>. (\<sigma> sp) \<noteq> 0);; (stmt.Seq (translate_program C sp vp) (translate_program B sp vp))), \<phi>'\<rangle> \<rightarrow> \<phi>'''"
                                  and asmnotfct: "\<langle>stmt.Assume (lnot (\<lambda>\<sigma>. (\<sigma> sp) \<noteq> 0)), \<phi>'''\<rangle> \<rightarrow> \<phi>''"
    unfolding while_cond_def
    by(auto del:single_sem_Assume_elim)
    from while_only have "\<exists>v'' \<sigma>''. \<phi>''' = transform_state_with_return_val v'' \<sigma>'' prev_stack vp" using phi'fct
    proof(induction "stmt.While (stmt.Assume (\<lambda>\<sigma>. (\<sigma> sp) \<noteq> 0);; (stmt.Seq (translate_program C sp vp) (translate_program B sp vp)))" \<phi>' \<phi>''' arbitrary: v' \<sigma>'' rule:single_sem.induct)
      case (SemWhileIter \<gamma> \<gamma>' \<gamma>'')
      from SemWhileIter have sig''fct: "\<gamma> = transform_state_with_return_val v' \<sigma>'' prev_stack vp" by auto
      from SemWhileIter have "\<langle>Assume (\<lambda>\<sigma>. \<sigma> sp \<noteq> 0) ;; (translate_program C sp vp ;; translate_program B sp vp), \<gamma>\<rangle> \<rightarrow> \<gamma>'" by auto
      from this obtain \<phi>'''' where cfct: "\<langle>(translate_program C sp vp), \<gamma>\<rangle> \<rightarrow> \<phi>''''"
                              and bfct: "\<langle>(translate_program B sp vp),  \<phi>''''\<rangle> \<rightarrow> \<gamma>'"
        by auto
      from sig''fct cfct While translated_program_step_state obtain \<gamma>''' u where  phi'''fct: "\<phi>'''' = transform_state_with_return_val u  \<gamma>''' prev_stack vp"
        by force
      from phi'''fct bfct While translated_program_step_state obtain \<gamma>'''' u' where  "\<gamma>' = transform_state_with_return_val u' \<gamma>'''' prev_stack vp"
        by force
      with SemWhileIter show ?case by blast
    next
      case (SemWhileExit \<gamma>)
      then show ?case by auto
    qed
    from this obtain v'' \<sigma>''' where phi'''fct: "\<phi>''' = transform_state_with_return_val v'' \<sigma>''' prev_stack vp" by force

    from asmnotfct while_only phi'''fct phi''fct phi'fct havocfct Bfct
    have "\<langle>stmt.While (stmt.Assume (\<lambda>\<sigma>. (\<sigma> sp) \<noteq> 0);; (stmt.Seq (translate_program C sp vp) (translate_program B sp vp))), transform_state_with_return_val v' \<sigma>'' prev_stack vp\<rangle> \<rightarrow> transform_state_with_return_val v'' \<sigma>''' prev_stack vp"
          and "\<langle>(translate_program B sp vp), transform_state_with_return_val v0 \<sigma> prev_stack vp \<rangle> \<rightarrow> transform_state_with_return_val v' \<sigma>'' prev_stack vp"
          and "\<langle>stmt.Assume (lnot (\<lambda>\<sigma>. (\<sigma> sp) \<noteq> 0)), transform_state_with_return_val v'' \<sigma>''' prev_stack vp\<rangle> \<rightarrow> transform_state_with_return_val v''' \<sigma>' prev_stack vp"
          and "\<langle>stmt.Havoc sp,  transform_state_with_return_val v''' \<sigma>' prev_stack vp\<rangle> \<rightarrow> transform_state_with_return_val v \<sigma>' prev_stack vp"
      by auto
    from this show ?case
    proof(induction "stmt.While (stmt.Assume (\<lambda>\<sigma>. (\<sigma> sp) \<noteq> 0);; (stmt.Seq (translate_program C sp vp) (translate_program B sp vp)))" "transform_state_with_return_val v' \<sigma>'' prev_stack vp" "transform_state_with_return_val v'' \<sigma>''' prev_stack vp" arbitrary: v0 \<sigma> v' \<sigma>'' v'' \<sigma>''' v''' v \<sigma>' rule:single_sem.induct)
      case (SemWhileIter \<gamma> vb \<gamma>')
      from SemWhileIter obtain \<gamma>'' where cfct:"\<langle>translate_program C sp vp, transform_state_with_return_val vb \<gamma>' prev_stack vp\<rangle> \<rightarrow> \<gamma>''"
                                      and bfct:"\<langle>translate_program B sp vp, \<gamma>''\<rangle> \<rightarrow> \<gamma>"
        by blast
      from asm cfct translated_program_step_state obtain u \<gamma>''' where gamma''fct: "\<gamma>'' = transform_state_with_return_val u \<gamma>''' prev_stack vp"
        by force
      from asm bfct gamma''fct translated_program_step_state obtain u' \<gamma>'''' where gammafct: "\<gamma> = transform_state_with_return_val u' \<gamma>'''' prev_stack vp"
        by force
      from bfct gamma''fct gammafct have "\<langle>translate_program B sp vp, transform_state_with_return_val u \<gamma>''' prev_stack vp\<rangle> \<rightarrow> transform_state_with_return_val u' \<gamma>'''' prev_stack vp"
        by auto
      with SemWhileIter gammafct have "\<langle>trm.While B C, \<gamma>'''\<rangle> \<Down> \<langle>v, \<sigma>'\<rangle>" by (auto)
      moreover from SemWhileIter While basm have bstep: "\<langle>B, \<sigma>\<rangle> \<Down> \<langle>vb, \<gamma>'\<rangle>" by metis
      moreover from casm cfct gamma''fct While have cstep: "\<langle>C, \<gamma>'\<rangle> \<Down> \<langle>u, \<gamma>'''\<rangle>" by metis
      moreover from SemWhileIter have "vb \<noteq> 0"
        apply(auto)
        by (metis asm state_transform_sp_acc)
      ultimately show ?case by (auto simp add:SemWhileTrue)
    next
      case (SemWhileExit vb)
      from SemWhileExit While basm have bstep: "\<langle>B, \<sigma>\<rangle> \<Down> \<langle>vb, \<sigma>''\<rangle>" by metis
      from SemWhileExit have asmnot: "\<langle>Assume (lnot (\<lambda>\<sigma>. \<sigma> sp \<noteq> 0)), transform_state_with_return_val v'' \<sigma>''' prev_stack vp\<rangle> \<rightarrow> transform_state_with_return_val v''' \<sigma>' prev_stack vp" by auto
      from asmnot have "\<sigma>''' = \<sigma>'" using state_transform_eq lnot_def asm add_leD1 
        by (metis single_sem_Assume_elim)
      moreover from asmnot have "v'' = 0" unfolding lnot_def 
        apply(auto)
        by (metis asm state_transform_sp_acc)
      moreover from SemWhileExit have  "\<sigma>''' = \<sigma>''" using state_transform_eq asm add_leD1 by (metis)
      moreover from SemWhileExit have  "vb = v''" using state_transform_eq asm add_leD1 by (metis)
      ultimately show ?case using \<open>\<langle>B, \<sigma>\<rangle> \<Down> \<langle>vb, \<sigma>''\<rangle>\<close> by(auto simp add:SemWhileFalse)
    qed
  qed
qed



theorem trm_translation_sem_equiv: "(\<langle>lhcC, \<sigma>\<rangle> \<Down> \<langle>v, \<sigma>'\<rangle> = (\<langle>program_translation lhcC, retval_state_translation 0 \<sigma> lhcC\<rangle> \<rightarrow> (retval_state_translation v \<sigma>' lhcC)))"
proof -
  note t = LHC_RHHL_sem_equiv_general[where prev_stack= "[]" and sp = "0" and vp = "1+(get_deepest_operation_depth lhcC)" and lhcC = "lhcC" and \<sigma>="\<sigma>" and v="v" and \<sigma>'="\<sigma>'"]
  thus ?thesis unfolding program_translation_def retval_state_translation_def by auto
qed


text\<open>Logical state is not meant to ever be accessed\<close>
definition hyper_pre_state_translation :: "hyper_term \<Rightarrow> hyper_store \<Rightarrow> val hyper_set"
  where 
"hyper_pre_state_translation Cs S = (\<lambda>i. {(undefined, retval_state_translation_partial 0 (S i) (map_of Cs i))})"

text\<open>Beware, the function does not return a hyper_set but rather sth like a hyper_store but in RHHL\<close>
definition hyper_post_state_translation :: "hyper_term \<Rightarrow> hyper_return_value \<Rightarrow> hyper_store \<Rightarrow> nat \<Rightarrow> val npstate"
  where 
"hyper_post_state_translation Cs V S = (\<lambda>i. (case map_of V i of (Some v) \<Rightarrow> (retval_state_translation_partial v (S i) (map_of Cs i))
                                                                 |None    \<Rightarrow> (retval_state_translation_partial 0 (S i) (map_of Cs i))))"


fun hyper_post_state_translation_inv1 :: "(nat \<Rightarrow> val npstate) \<Rightarrow> hyper_term \<Rightarrow> hyper_return_value"
  where 
"hyper_post_state_translation_inv1 S [] = []" |
"hyper_post_state_translation_inv1 S ((i, _)#Cs) = (i,S i 0)#(hyper_post_state_translation_inv1 S Cs)"

fun post_state_translation_inv2 :: "val npstate \<Rightarrow> trm option \<Rightarrow> store" where
"post_state_translation_inv2 \<sigma> None x = \<sigma> (x + 1)" |
"post_state_translation_inv2 \<sigma> (Some C) x = \<sigma> (x + (1 + get_deepest_operation_depth C))"

definition hyper_post_state_translation_inv2 :: "hyper_term \<Rightarrow> (nat \<Rightarrow> val npstate) \<Rightarrow> hyper_store"
  where 
"hyper_post_state_translation_inv2 Cs S = (\<lambda>i. post_state_translation_inv2 (S i) (map_of Cs i))"


lemma post_trans_inv: "post_state_translation_inv2 (retval_state_translation_partial 0 (\<sigma>) C) C = \<sigma>"
proof(rule ext)
  fix x
  show "post_state_translation_inv2 (retval_state_translation_partial 0 \<sigma> C) C x = \<sigma> x"
  proof (cases C)
    case None
    then show ?thesis  by(auto simp add:transform_state_with_return_val_def)
  next
    case (Some C')
    show ?thesis using \<open>C = Some C'\<close> by(auto simp add:retval_state_translation_def transform_state_with_return_val_def)
  qed
qed


lemma map_find: "(map_of l i = None) = (find (\<lambda>(j,_). i = j) l = None)"
proof (induction l)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  then show ?case by(auto)
qed


lemma map_find_some: "(map_of l i = Some x) \<Longrightarrow> (find (\<lambda>(i',x'). i = i' \<and> x = x') l = Some (i, x)) "
proof (induction l)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  then show ?case 
    by (smt (verit, best) case_prodE case_prodI2 find.simps(2) map_of_Cons_code(2) option.inject)
qed


lemma hyper_trans_inv_none: "map_of (hyper_post_state_translation_inv1 S Cs) i = None \<longleftrightarrow> map_of Cs i = None"
  unfolding map_find
proof (induction Cs)
  case Nil
  then show ?case by simp
next
  case (Cons a Cs)
  then show ?case by auto
qed

lemma hyper_trans_inv_rev: "(map_of (hyper_post_state_translation_inv1 S Cs) i = Some x) \<Longrightarrow> (S i 0 = x)"
proof -
  assume "(map_of (hyper_post_state_translation_inv1 S Cs) i = Some x)"
  hence "(find (\<lambda>(i',x'). i = i' \<and> x = x') (hyper_post_state_translation_inv1 S Cs) = Some (i, x))" using map_find_some by force
  thus "(S i 0 = x)"
  proof(induction Cs)
    case Nil
    then show ?case by simp
  next
    case (Cons a Cs)
    then show ?case
      by (smt (verit, best) find.simps(2) hyper_post_state_translation_inv1.elims list.discI list.inject option.inject prod.inject)
  qed
qed


definition hyper_program_translation  :: "hyper_term \<Rightarrow> val hyper_program" where 
"hyper_program_translation Cs = (\<lambda>i. (case map_of Cs i of 
                                      (Some C) \<Rightarrow> (Some (program_translation C))
                                      | None \<Rightarrow> None
                                ))"


definition equiv_prec_wrtt :: "hyper_assertion \<Rightarrow> hyper_term \<Rightarrow> val rel_hyper_assertion " where
"equiv_prec_wrtt lhcP lhcCs = (\<lambda>S. (\<exists>S'. S = hyper_pre_state_translation lhcCs S' \<and> (lhcP S')))"


definition post_state_combinations :: "val hyper_set \<Rightarrow> (nat \<Rightarrow> val npstate) set" where
  "post_state_combinations S = {S'. \<forall>i. \<exists>l. (l, S' i) \<in> S i}"

definition equiv_post_wrtt :: "post_hyper_assertion \<Rightarrow> hyper_term \<Rightarrow> val rel_hyper_assertion " where
"equiv_post_wrtt lhcQ Cs = (\<lambda>S. \<forall>S'\<in>(post_state_combinations S). (\<forall>V S''. dom (map_of V) = dom (map_of Cs) \<and> S' = hyper_post_state_translation Cs V S'' \<longrightarrow> (lhcQ V S'')))"



lemma retval_state_translation_inj: "\<forall>v \<sigma> v' \<sigma>'. retval_state_translation v \<sigma> C = retval_state_translation v' \<sigma>' C \<longrightarrow> v = v' \<and> \<sigma> = \<sigma>'"
  unfolding retval_state_translation_def 
  using state_transform_eq
  by (metis diff_zero le_iff_add length_0_conv)
  

lemma hyper_post_state_translation_inj: "\<forall>V S V' S' Cs. hyper_post_state_translation Cs V S = hyper_post_state_translation Cs V' S' \<and> dom (map_of V) = dom (map_of V') \<longrightarrow> (map_of V) = (map_of V') \<and> S = S'"
  unfolding hyper_post_state_translation_def
proof(intro allI ballI impI conjI, elim conjE)
  show "\<And>V S V' S' Cs.
       \<lbrakk>(\<lambda>i. case map_of V i of None \<Rightarrow> retval_state_translation_partial 0 (S i) (map_of Cs i)
             | Some v \<Rightarrow> retval_state_translation_partial v (S i) (map_of Cs i)) =
        (\<lambda>i. case map_of V' i of None \<Rightarrow> retval_state_translation_partial 0 (S' i) (map_of Cs i)
              | Some v \<Rightarrow> retval_state_translation_partial v (S' i) (map_of Cs i));
        dom (map_of V) = dom (map_of V')\<rbrakk>
       \<Longrightarrow> map_of V = map_of V'"
  proof
    fix V S V' S' Cs i
    assume "(\<lambda>i. case map_of V i of None \<Rightarrow> retval_state_translation_partial 0 (S i) (map_of Cs i)
             | Some v \<Rightarrow> retval_state_translation_partial v (S i) (map_of Cs i)) =
        (\<lambda>i. case map_of V' i of None \<Rightarrow> retval_state_translation_partial 0 (S' i) (map_of Cs i)
              | Some v \<Rightarrow> retval_state_translation_partial v (S' i) (map_of Cs i))"
    hence asmf: "(case map_of V i of None \<Rightarrow> retval_state_translation_partial 0 (S i) (map_of Cs i)
             | Some v \<Rightarrow> retval_state_translation_partial v (S i) (map_of Cs i)) =
        (case map_of V' i of None \<Rightarrow> retval_state_translation_partial 0 (S' i) (map_of Cs i)
              | Some v \<Rightarrow> retval_state_translation_partial v (S' i) (map_of Cs i))" by metis
    assume "dom (map_of V) = dom (map_of V')"
    with asmf show "map_of V i = map_of V' i"
      apply(auto split:option.splits)
    proof(cases "(map_of Cs i)")
      case None
      then show "\<And>x2 x2a.
       \<lbrakk>dom (map_of V) = dom (map_of V'); map_of V' i = Some x2; map_of V i = Some x2a;
        retval_state_translation_partial x2a (S i) (map_of Cs i) = retval_state_translation_partial x2 (S' i) (map_of Cs i); map_of Cs i = None\<rbrakk>
       \<Longrightarrow> x2a = x2" using state_transform_eq by auto
    next
      case (Some a)
      then show "\<And>x2 x2a a.
       \<lbrakk>dom (map_of V) = dom (map_of V'); map_of V' i = Some x2; map_of V i = Some x2a;
        retval_state_translation_partial x2a (S i) (map_of Cs i) = retval_state_translation_partial x2 (S' i) (map_of Cs i); map_of Cs i = Some a\<rbrakk>
       \<Longrightarrow> x2a = x2" using retval_state_translation_inj by auto
    qed
  qed 
next
  show "\<And>V S V' S' Cs.
       (\<lambda>i. case map_of V i of None \<Rightarrow> retval_state_translation_partial 0 (S i) (map_of Cs i)
             | Some v \<Rightarrow> retval_state_translation_partial v (S i) (map_of Cs i)) =
       (\<lambda>i. case map_of V' i of None \<Rightarrow> retval_state_translation_partial 0 (S' i) (map_of Cs i)
             | Some v \<Rightarrow> retval_state_translation_partial v (S' i) (map_of Cs i)) \<and>
       dom (map_of V) = dom (map_of V') \<Longrightarrow>
       S = S'"
  proof(rule ext, elim conjE)
  fix V S V' S' Cs i
    assume "(\<lambda>i. case map_of V i of None \<Rightarrow> retval_state_translation_partial 0 (S i) (map_of Cs i)
             | Some v \<Rightarrow> retval_state_translation_partial v (S i) (map_of Cs i)) =
        (\<lambda>i. case map_of V' i of None \<Rightarrow> retval_state_translation_partial 0 (S' i) (map_of Cs i)
              | Some v \<Rightarrow> retval_state_translation_partial v (S' i) (map_of Cs i))"
    hence asmf: "(case map_of V i of None \<Rightarrow> retval_state_translation_partial 0 (S i) (map_of Cs i)
             | Some v \<Rightarrow> retval_state_translation_partial v (S i) (map_of Cs i)) =
        (case map_of V' i of None \<Rightarrow> retval_state_translation_partial 0 (S' i) (map_of Cs i)
              | Some v \<Rightarrow> retval_state_translation_partial v (S' i) (map_of Cs i))" by metis
    with asmf show "S i = S' i"
      apply(cases "(map_of Cs i)")
      apply(auto split:option.splits)
      using state_transform_eq  apply(simp_all)
      using retval_state_translation_inj
         apply meson
      using retval_state_translation_inj
        apply meson
      using retval_state_translation_inj
       apply meson
      using retval_state_translation_inj
      apply meson
      done
  qed
qed

lemma cs_v_dom_eq: "\<langle>Cs, S\<rangle> \<Down> \<langle>V, S'\<rangle> \<Longrightarrow>  dom (map_of Cs) = dom (map_of V)"
  unfolding big_sem_hyper_def dom_def
  by (metis (mono_tags, lifting) mem_Collect_eq option.distinct(1))


theorem LHC_RHHL_hypertriple_equivalence: "\<Turnstile>LHC {P} [Cs] {Q} \<longleftrightarrow> \<Turnstile> {equiv_prec_wrtt P Cs} [hyper_program_translation Cs] {equiv_post_wrtt Q Cs}"
  unfolding valid_def relational_hyper_hoare_triple_def hyper_hoare_triple_def imp_def
proof(intro impI ballI allI iffI)
  fix S
  assume asm1: "\<forall>S. P S \<longrightarrow> wp Cs Q S"
  assume "equiv_prec_wrtt P Cs S"
  from this obtain S' where S_eq:"(S = hyper_pre_state_translation Cs S')" and "(P S')" unfolding equiv_prec_wrtt_def by blast
  with asm1 have  "wp Cs Q S'" by auto
  hence asm1_unf:"(\<forall>S'' V. \<langle>Cs, S'\<rangle> \<Down> \<langle>V, S''\<rangle> \<longrightarrow> Q V S'')" unfolding wp_def by auto
  let ?S' = "(sem_lifted (hyper_program_translation Cs) (hyper_pre_state_translation Cs S'))"
  from trm_translation_sem_equiv have "\<forall>S'''\<in>(post_state_combinations (?S')). (let V = hyper_post_state_translation_inv1 S''' Cs in let S'' = hyper_post_state_translation_inv2 Cs S''' in S''' = hyper_post_state_translation Cs V S'' \<and> \<langle>Cs, S'\<rangle> \<Down> \<langle>V, S''\<rangle>)"
    apply(auto simp add: post_state_combinations_def hyper_program_translation_def hyper_pre_state_translation_def hyper_post_state_translation_inv2_def hyper_post_state_translation_def big_sem_hyper_def dom_def sem_lifted_def sem_def Let_def split:option.splits)
       apply(rule ext)
       apply(auto split:option.splits simp add:hyper_trans_inv_none)
      apply(rule ext)
      apply(auto simp add: post_trans_inv hyper_trans_inv_rev transform_state_with_return_val_def)
  proof
    fix S''' i x x2
    assume asm: "\<forall>i. (map_of Cs i = None \<longrightarrow> S''' i = (\<lambda>ia. if ia = 0 then 0 else if ia < Suc 0 then 0 else S' i (ia - Suc 0))) \<and>
            (\<forall>x2. map_of Cs i = Some x2 \<longrightarrow> \<langle>program_translation x2, retval_state_translation 0 (S' i) x2\<rangle> \<rightarrow> S''' i)"
    assume "map_of (hyper_post_state_translation_inv1 S''' Cs) i = Some x2"
    with hyper_trans_inv_rev have fct: "S''' i 0 = x2" by auto
    show "S''' i x = retval_state_translation_partial x2 (post_state_translation_inv2 (S''' i) (map_of Cs i)) (map_of Cs i) x"
    proof(cases "(map_of Cs i)")
      case None
      then show ?thesis by(auto simp add:transform_state_with_return_val_def fct)
    next
      case (Some C)
      with asm have "\<langle>program_translation C, retval_state_translation 0 (S' i) C\<rangle> \<rightarrow> S''' i" by auto
      with translated_program_step_state obtain u \<gamma> where fct2: "S''' i = transform_state_with_return_val u \<gamma> [] (1 + get_deepest_operation_depth C)" 
        unfolding retval_state_translation_def using program_translation_def by fastforce
      from \<open>map_of Cs i = Some C\<close> show ?thesis apply(auto simp add:retval_state_translation_def transform_state_with_return_val_def fct)
        using fct2 by(auto simp add:transform_state_with_return_val_def)
    qed
  next
    fix S''' i y
    assume asm1: "\<forall>i. (map_of Cs i = None \<longrightarrow> S''' i = (\<lambda>ia. if ia = 0 then 0 else if ia < Suc 0 then 0 else S' i (ia - Suc 0))) \<and>
            (\<forall>x2. map_of Cs i = Some x2 \<longrightarrow> \<langle>program_translation x2, retval_state_translation 0 (S' i) x2\<rangle> \<rightarrow> S''' i)"
    assume asm2: "map_of Cs i = Some y"
    with hyper_trans_inv_none obtain v where fact1: "map_of (hyper_post_state_translation_inv1 S''' Cs) i = Some v" by force
    with hyper_trans_inv_rev have fct: "S''' i 0 = v" by auto
    have "S''' i = retval_state_translation_partial v (post_state_translation_inv2 (S''' i) (map_of Cs i)) (map_of Cs i)"
      apply(rule ext)
    proof(cases "(map_of Cs i)")
      fix x
      case None
      then show "S''' i x = retval_state_translation_partial v (post_state_translation_inv2 (S''' i) (map_of Cs i)) (map_of Cs i) x" by(auto simp add:transform_state_with_return_val_def fct)
    next
      fix x
      case (Some C)
      with asm1 have "\<langle>program_translation C, retval_state_translation 0 (S' i) C\<rangle> \<rightarrow> S''' i" by auto
      with translated_program_step_state obtain u \<gamma> where fct2: "S''' i = transform_state_with_return_val u \<gamma> [] (1 + get_deepest_operation_depth C)" 
        unfolding retval_state_translation_def using program_translation_def by fastforce
      from \<open>map_of Cs i = Some C\<close> show "S''' i x = retval_state_translation_partial v (post_state_translation_inv2 (S''' i) (map_of Cs i)) (map_of Cs i) x"
        apply(auto simp add:retval_state_translation_def transform_state_with_return_val_def fct)
        using fct2 by(auto simp add:transform_state_with_return_val_def)
    qed
    with asm1 asm2 have fact2: "\<langle>program_translation
                  y, retval_state_translation 0 (S' i) y\<rangle> \<rightarrow> retval_state_translation v (post_state_translation_inv2 (S''' i) (Some y)) y" by auto
    from fact1 fact2 show "\<exists>v. map_of (hyper_post_state_translation_inv1 S''' Cs) i = Some v \<and>
                \<langle>program_translation
                  y, retval_state_translation 0 (S' i) y\<rangle> \<rightarrow> retval_state_translation v (post_state_translation_inv2 (S''' i) (Some y)) y" by auto
  qed
  with hyper_post_state_translation_inj cs_v_dom_eq have "\<forall>S'''\<in>(post_state_combinations (?S')). (\<forall>V S''. dom (map_of V) = dom (map_of Cs) \<and> S''' = hyper_post_state_translation Cs V S'' \<longrightarrow> \<langle>Cs, S'\<rangle> \<Down> \<langle>V, S''\<rangle>)"
    by (smt (verit, ccfv_SIG) big_sem_hyper_def)
  with asm1_unf S_eq show " equiv_post_wrtt Q Cs (sem_lifted (hyper_program_translation Cs) S)" unfolding equiv_post_wrtt_def by blast
next
  fix S
  assume asm1: "\<forall>S. equiv_prec_wrtt P Cs S \<longrightarrow> equiv_post_wrtt Q Cs (sem_lifted (hyper_program_translation Cs) S)"
  assume asm2: "P S"
  let ?S' = "hyper_pre_state_translation Cs S"
  from asm2 have asm2_fact: "equiv_prec_wrtt P Cs ?S'" using equiv_prec_wrtt_def by auto
  let ?S'' = "(sem_lifted (hyper_program_translation Cs) ?S')"
  from asm2_fact asm1 have "equiv_post_wrtt Q Cs ?S''" unfolding equiv_post_wrtt_def by auto
  moreover from trm_translation_sem_equiv have "\<forall>S' V. \<langle>Cs, S\<rangle> \<Down> \<langle>V, S'\<rangle> \<longrightarrow> (hyper_post_state_translation Cs V S')\<in>(post_state_combinations ?S'')" 
    apply(auto simp add: big_sem_hyper_def hyper_post_state_translation_def post_state_combinations_def sem_lifted_def hyper_program_translation_def hyper_pre_state_translation_def sem_def split:option.splits)
    apply (simp add: domIff)
    apply (meson domI domIff)
    done
  ultimately show "wp Cs Q S" unfolding wp_def equiv_post_wrtt_def using cs_v_dom_eq by blast
qed



end