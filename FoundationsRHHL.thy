text \<open>2 Foundations of RHHL\<close>
theory FoundationsRHHL
  imports "HHL/Loops"  "HOL-Library.While_Combinator" "HOL-Computational_Algebra.Primes" "HOL-Library.FuncSet"
begin

section \<open>2.1 Programming language and semantics\<close>

text\<open>PVars\<close>
type_synonym var = nat

text\<open>PVals are defined as an arbitrary type\<close>

text\<open>Program state\<close>
type_synonym 'a npstate = "(var, 'a) pstate"

text\<open>Both language and its semantics are defined in HHL/Language as they were directly adopted from HHL\<close>


text\<open>Defintions of the if-else and while commands you can find in HHL/Loops as if_then_else and while_cond\<close>

text\<open>Definition of the if command
    - the missing else branch is represented with the Skip command\<close>
definition if_then_else_skip where
"if_then_else_skip b C = if_then_else b C Skip "

notation if_then_else  ("IF _ THEN _ ELSE _" [0, 0, 61] 61)
notation if_then_else_skip  ("IF _  THEN _ FI" [0, 60] 61)
notation while_cond  ("WHILE _ DO _" [0, 61] 61)





section\<open>2.2 Relational hyper-triples\<close>

text\<open>Definition 2.1 (Logical states and extended states) \<close>
type_synonym 'a nstate = "(var, 'a, var, 'a) state"

text\<open>Definition 2.2 (Hyper-sets and relational hyper-assertions)\<close>
type_synonym 'a hyper_set = "nat \<Rightarrow> 'a nstate set"
type_synonym 'a rel_hyper_assertion = "'a hyper_set \<Rightarrow> bool"

text\<open>Definition 2.3 (Hyper-programs) \<close>
type_synonym 'a hyper_program = "nat \<rightharpoonup> (var, 'a) stmt"

text\<open>Definition 2.4 (Extended semantics)\<close>
text\<open>Extended semantics are defined in HHL/Language as the definition was directly adopted from HHL\<close>

text\<open>Definition 2.5 (Relational extended semantics)\<close>
fun partial_sem where
  "partial_sem (Some C) S = sem C S"
| "partial_sem None S = S"

definition sem_rel :: "'a hyper_program \<Rightarrow> 'a hyper_set \<Rightarrow> 'a hyper_set" where
  "sem_rel Cs Ss i = partial_sem (Cs i) (Ss i)"

text\<open>Definition 2.6 (Relational hyper-triples)\<close>
definition relational_hyper_hoare_triple
:: "'a rel_hyper_assertion \<Rightarrow> 'a hyper_program \<Rightarrow> 'a rel_hyper_assertion \<Rightarrow> bool"

 ("\<Turnstile> {_} [_] {_}" [51,0,0] 81) where
  "\<Turnstile> {P} [l] {Q} \<longleftrightarrow> (\<forall>S. P S \<longrightarrow> Q (sem_rel l S))"


lemma relational_hyper_hoare_tripleI:
  assumes "\<And>S. P S \<Longrightarrow> Q (sem_rel l S)"
  shows "\<Turnstile> {P} [l] {Q}"
  using assms relational_hyper_hoare_triple_def
  by blast

lemma relational_hyper_hoare_tripleE:
  assumes "\<Turnstile> {P} [l] {Q}"
      and "P S"
    shows "Q (sem_rel l S)"
  by (meson assms(1) assms(2) relational_hyper_hoare_triple_def)



section\<open>2.4 Syntactic relational hyper-assertions\<close>

text \<open>Quantified variables and quantified states are represented as de Bruijn indices (natural numbers).\<close>
type_synonym qstate = nat
type_synonym qvar = nat

text\<open>Definition 2.7 (Syntactic hyper-expressions) \<close>
type_synonym 'a binop = "'a \<Rightarrow> 'a \<Rightarrow> 'a"

datatype 'a exp =
  EPVar qstate var    \<comment>\<open>\<open>\<phi>\<^sup>P(x)\<close>: Program variable\<close>
  | ELVar qstate var  \<comment>\<open>\<open>\<phi>\<^sup>L(x)\<close>: Logical variable\<close>
  | EQVar qvar        \<comment>\<open>\<open>y\<close>: Quantified variable\<close>
  | EConst 'a
  | EBinop "'a exp" "'a binop" "'a exp" \<comment>\<open>\<open>e \<oplus> e\<close>\<close>
  | EFun "'a \<Rightarrow> 'a" "'a exp"            \<comment>\<open>\<open>f(e)\<close>\<close>

text\<open>Definition 2.8 (Syntactic relational hyper-assertions) \<close>
type_synonym 'a comp = "'a \<Rightarrow> 'a \<Rightarrow> bool"

text \<open>Quantified variables and quantified states are represented as de Bruijn indices (natural numbers).
Thus, quantifiers do not have a name for the variable or state they quantify over.\<close>
datatype 'a syn_assertion =
  AConst bool
  | AComp "'a exp" "'a comp" "'a exp"  \<comment>\<open>\<open>e \<succeq> e\<close>\<close>            
  | AForallState nat "'a syn_assertion"        \<comment>\<open>\<open>\<forall><\<phi>>i. A\<close>\<close>  
  | AExistsState nat "'a syn_assertion"        \<comment>\<open>\<open>\<exists><\<phi>>i. A\<close>\<close>  
  | AForall "'a syn_assertion"             \<comment>\<open>\<open>\<forall>y. A\<close>\<close>        
  | AExists "'a syn_assertion"             \<comment>\<open>\<open>\<exists>y. A\<close>\<close>         
  | AOr "'a syn_assertion" "'a syn_assertion"  \<comment>\<open>\<open>A \<or> A\<close>\<close>     
  | AAnd "'a syn_assertion" "'a syn_assertion" \<comment>\<open>\<open>A \<and> A\<close>\<close>     


text \<open>We use a list of values and a list of states to track quantified values and states, respectively.\<close>
fun interp_exp :: "'a list \<Rightarrow> 'a nstate list \<Rightarrow> 'a exp \<Rightarrow> 'a" where
  "interp_exp vals states (EPVar st x) = snd (states ! st) x"
| "interp_exp vals states (ELVar st x) = fst (states ! st) x"
| "interp_exp vals states (EQVar x) = vals ! x"
| "interp_exp vals states (EConst v) = v"
| "interp_exp vals states (EBinop e1 op e2) = op (interp_exp vals states e1) (interp_exp vals states e2)"
| "interp_exp vals states (EFun f e) = f (interp_exp vals states e)"


fun sat_assertion :: "'a list \<Rightarrow> 'a nstate list \<Rightarrow> 'a syn_assertion \<Rightarrow> 'a hyper_set \<Rightarrow> bool" where
  "sat_assertion vals states (AConst b) _ \<longleftrightarrow> b"
| "sat_assertion vals states (AComp e1 cmp e2) _ \<longleftrightarrow> cmp (interp_exp vals states e1) (interp_exp vals states e2)"
| "sat_assertion vals states (AForallState i A) S \<longleftrightarrow> (\<forall>\<phi> \<in> S i. sat_assertion vals (\<phi> # states) A S)"
| "sat_assertion vals states (AExistsState i A) S \<longleftrightarrow> (\<exists>\<phi> \<in> S i. sat_assertion vals (\<phi> # states) A S)"
| "sat_assertion vals states (AForall A) S \<longleftrightarrow> (\<forall>v. sat_assertion (v # vals) states A S)"
| "sat_assertion vals states (AExists A) S \<longleftrightarrow> (\<exists>v. sat_assertion (v # vals) states A S)"
| "sat_assertion vals states (AAnd A B) S \<longleftrightarrow> (sat_assertion vals states A S \<and> sat_assertion vals states B S)"
| "sat_assertion vals states (AOr A B) S \<longleftrightarrow> (sat_assertion vals states A S \<or> sat_assertion vals states B S)"


text \<open>Negation and implication are defined on top of this base language.\<close>
definition neg_cmp :: "'a comp \<Rightarrow> 'a comp" where
  "neg_cmp cmp v1 v2 \<longleftrightarrow> \<not> (cmp v1 v2)"

fun ANot where
  "ANot (AConst b) = AConst (\<not> b)"
| "ANot (AComp e1 cmp e2) = AComp e1 (neg_cmp cmp) e2"
| "ANot (AForallState i A) = AExistsState i (ANot A)"
| "ANot (AExistsState i A) = AForallState i (ANot A)"
| "ANot (AOr A B) = AAnd (ANot A) (ANot B)"
| "ANot (AAnd A B) = AOr (ANot A) (ANot B)"
| "ANot (AForall A) = AExists (ANot A)"
| "ANot (AExists A) = AForall (ANot A)"

definition AImp where
  "AImp A B = AOr (ANot A) B"

lemma sat_assertion_Not:
  "sat_assertion vals states (ANot A) S \<longleftrightarrow> \<not>(sat_assertion vals states A S)"
  by (induct A arbitrary: vals states) (simp_all add: neg_cmp_def)

lemma sat_assertion_Imp:
  "sat_assertion vals states (AImp A B) S \<longleftrightarrow> (sat_assertion vals states A S \<longrightarrow> sat_assertion vals states B S)"
  by (simp add: AImp_def sat_assertion_Not)

abbreviation interp_assert where "interp_assert \<equiv> sat_assertion [] []"


subsection\<open>Syntactic programs\<close>

text \<open>Syntactic program expressions\<close>
datatype 'a pexp =
  PVar var \<comment>\<open>Normal variable, like x\<close>
  | PConst 'a
  | PBinop "'a pexp" "'a binop" "'a pexp"
  | PFun "'a \<Rightarrow> 'a" "'a pexp"

fun interp_pexp :: "'a pexp \<Rightarrow> 'a npstate \<Rightarrow> 'a"
  where
  "interp_pexp (PVar x) \<phi> = \<phi> x"
| "interp_pexp (PConst n) _ = n"
| "interp_pexp (PBinop p1 op p2) \<phi> = op (interp_pexp p1 \<phi>) (interp_pexp p2 \<phi>)"
| "interp_pexp (PFun f p) \<phi> = f (interp_pexp p \<phi>)"

fun pexp_to_exp where
  "pexp_to_exp st (PVar x) = EPVar st x"
| "pexp_to_exp _ (PConst n) = EConst n"
| "pexp_to_exp st (PBinop p1 op p2) = EBinop (pexp_to_exp st p1) op (pexp_to_exp st p2)"
| "pexp_to_exp st (PFun f p) = EFun f (pexp_to_exp st p)"

lemma same_syn_sem_exp:
  "interp_pexp p (snd (states ! st)) = interp_exp vals states (pexp_to_exp st p)"
proof (induct p)
  case (PVar x)
  then show ?case
    using hd_conv_nth by force
qed (simp_all)


text \<open>Syntactic program expressions (booleans)\<close>
datatype 'a pbexp =
  PBConst bool
  | PBAnd "'a pbexp" "'a pbexp"
  | PBOr "'a pbexp" "'a pbexp"
  | PBComp "'a pexp" "'a comp" "'a pexp"

fun interp_pbexp :: "'a pbexp \<Rightarrow> 'a npstate \<Rightarrow> bool"
  where
  "interp_pbexp (PBConst b) _ \<longleftrightarrow> b"
| "interp_pbexp (PBAnd pb1 pb2) \<phi> \<longleftrightarrow> interp_pbexp pb1 \<phi> \<and> interp_pbexp pb2 \<phi>"
| "interp_pbexp (PBOr pb1 pb2) \<phi> \<longleftrightarrow> interp_pbexp pb1 \<phi> \<or> interp_pbexp pb2 \<phi>"
| "interp_pbexp (PBComp p1 cmp p2) \<phi> \<longleftrightarrow> cmp (interp_pexp p1 \<phi>) (interp_pexp p2 \<phi>)"

fun pbexp_to_assertion where
  "pbexp_to_assertion _ (PBConst b) = AConst b"
| "pbexp_to_assertion st (PBAnd pb1 pb2) = AAnd (pbexp_to_assertion st pb1) (pbexp_to_assertion st pb2)"
| "pbexp_to_assertion st (PBOr pb1 pb2) = AOr (pbexp_to_assertion st pb1) (pbexp_to_assertion st pb2)"
| "pbexp_to_assertion st (PBComp p1 cmp p2) = AComp (pexp_to_exp st p1) cmp (pexp_to_exp st p2)"


lemma same_syn_sem_assertion:
  "interp_pbexp pb (snd (states ! st)) = sat_assertion vals states (pbexp_to_assertion st pb) S"
proof (induct pb)
  case (PBComp x1 x2 x3)
  then show ?case
    by (metis interp_pbexp.simps(4) pbexp_to_assertion.simps(4) same_syn_sem_exp sat_assertion.simps(2))
qed (simp_all)


text\<open>Syntactic programs\<close>
datatype 'a syn_stmt = 
  AssignS var "'a pexp"
  | SeqS "'a syn_stmt" "'a syn_stmt"                   
  | IfS "'a syn_stmt" "'a syn_stmt"                    
  | SkipS
  | HavocS var                                                
  | AssumeS "'a pbexp"
  | WhileS "'a syn_stmt"                                   


fun interp_syn_stmt :: "'a syn_stmt \<Rightarrow> (var, 'a) stmt" where
"interp_syn_stmt (AssignS v pe) = (Assign v (interp_pexp pe))" |
"interp_syn_stmt (SeqS C1 C2) = (Seq (interp_syn_stmt C1) (interp_syn_stmt C2))" |
"interp_syn_stmt (IfS C1 C2) = (If (interp_syn_stmt C1) (interp_syn_stmt C2))" |
"interp_syn_stmt (SkipS) = Skip" |
"interp_syn_stmt (HavocS v) = (Havoc v)" |
"interp_syn_stmt (AssumeS pb) = (Assume (interp_pbexp pb))" |
"interp_syn_stmt (WhileS C) = (interp_syn_stmt C)"


end