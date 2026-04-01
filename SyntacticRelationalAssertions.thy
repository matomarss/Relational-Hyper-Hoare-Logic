section \<open>Syntactic Relational Assertions\<close>

theory SyntacticRelationalAssertions
  imports Logic Loops ProgramHyperproperties Compositionality "~~/src/HOL/Library/While_Combinator" "HOL-Computational_Algebra.Primes"
begin

subsection \<open>Preliminaries: Types, expressions, 'a syn_assertions\<close>

type_synonym var = nat
type_synonym qstate = nat
type_synonym qvar = nat

type_synonym 'a nstate = "(var, 'a, var, 'a) state"
type_synonym 'a npstate = "(var, 'a) pstate"

type_synonym 'a binop = "'a \<Rightarrow> 'a \<Rightarrow> 'a"
type_synonym 'a comp = "'a \<Rightarrow> 'a \<Rightarrow> bool"


type_synonym 'a hyper_program = "nat \<rightharpoonup> (nat, 'a) stmt"
type_synonym 'a hyper_set = "nat \<Rightarrow> 'a nstate set"
type_synonym 'a rel_hyper_assertion = "'a hyper_set \<Rightarrow> bool"


text \<open>Quantified variables and quantified states are represented as de Bruijn indices (natural numbers).\<close>

datatype 'a exp =
  EPVar qstate var    \<comment>\<open>\<open>\<phi>\<^sup>P(x)\<close>: Program variable\<close>
  | ELVar qstate var  \<comment>\<open>\<open>\<phi>\<^sup>L(x)\<close>: Logical variable\<close>
  | EQVar qvar        \<comment>\<open>\<open>y\<close>: Quantified variable\<close>
  | EConst 'a
  | EBinop "'a exp" "'a binop" "'a exp" \<comment>\<open>\<open>e \<oplus> e\<close>\<close>
  | EFun "'a \<Rightarrow> 'a" "'a exp"            \<comment>\<open>\<open>f(e)\<close>\<close>

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



subsection \<open>Split\<close>

(* Works for every union
\<longrightarrow> k becomes k and k + 1
Above this is "shifted"
 *)
fun split where
  "split _ (AConst b) = AConst b"
| "split _ (AComp e1 cmp e2) = AComp e1 cmp e2"

| "split k (AOr A B) = AOr (split k A) (split k B)"
| "split k (AAnd A B) = AAnd (split k A) (split k B)"
| "split k (AForall A) = AForall (split k A)"
| "split k (AExists A) = AExists (split k A)"

| "split k (AForallState i A) = (if i = k then AAnd (AForallState k (split k A)) (AForallState (Suc k) (split k A))
  else AForallState (if i > k then Suc i else i) (split k A))"
| "split k (AExistsState i A) = (if i = k then AOr (AExistsState k (split k A)) (AExistsState (Suc k) (split k A))
  else AExistsState (if i > k then Suc i else i) (split k A))"

definition is_split where
  "is_split k old_sets new_sets \<longleftrightarrow>
  (old_sets k = new_sets k \<union> new_sets (Suc k)) \<and>
  (\<forall>i. i < k \<longrightarrow> new_sets i = old_sets i) \<and>
  (\<forall>i. i > Suc k \<longrightarrow> new_sets i = old_sets (i - 1))"

lemma is_split_simpleE:
  assumes "is_split k old_sets new_sets"
  shows "old_sets k = new_sets k \<union> new_sets (Suc k)"
  using assms unfolding is_split_def
  by argo

lemma is_split_smallerE:
  assumes "is_split k old_sets new_sets"
      and "i < k"
  shows "new_sets i = old_sets i"
  using assms unfolding is_split_def
  by blast

lemma is_split_largerE:
  assumes "is_split k old_sets new_sets"
      and "i > k"
  shows "new_sets (Suc i) = old_sets i"
  using assms unfolding is_split_def
  by auto



lemma split_soundness:
  assumes "is_split k old_sets new_sets"
    shows "sat_assertion vals states A old_sets \<longleftrightarrow> sat_assertion vals states (split k A) new_sets"
  using assms
proof (induct A arbitrary: vals states)
  case (AForallState i A)
  then show ?case
    apply (cases "i = k")
      unfolding sat_assertion.simps split.simps
      using AForallState(1)[OF AForallState(2), of vals] is_split_simpleE[OF assms] apply fastforce
    apply (cases "i < k")
      unfolding sat_assertion.simps split.simps
      using is_split_smallerE[OF assms] AForallState(1)[OF AForallState(2), of vals] apply simp
    unfolding sat_assertion.simps split.simps
      using assms is_split_largerE[OF assms] AForallState(1)[OF AForallState(2), of vals] by simp
next
  case (AExistsState i A)
  then show ?case
    apply (cases "i = k")
      unfolding sat_assertion.simps split.simps
      using AExistsState(1)[OF AExistsState(2), of vals] is_split_simpleE[OF assms] apply fastforce
    apply (cases "i < k")
      unfolding sat_assertion.simps split.simps
      using is_split_smallerE[OF assms] AExistsState(1)[OF AExistsState(2), of vals] apply simp
    unfolding sat_assertion.simps split.simps
      using assms is_split_largerE[OF assms] AExistsState(1)[OF AExistsState(2), of vals] by simp
qed (simp_all)








section \<open>Semantic Relational HHL\<close>


(*
definition relational_hyper_hoare_triple
 ("\<Turnstile> {_} [_] {_}" [51,0,0] 81) where
  "\<Turnstile> {P} [l] {Q} \<longleftrightarrow> (\<forall>S. P S \<longrightarrow> Q (List.map (\<lambda>p. sem (fst p) (snd p)) (zip l S)))"
*)

(* Infinite S, and then S untouched on... ? *)

(* l: *partial* function from nat to programs... *)

(*
Cs: partial function
Ss: total function
*) 

fun partial_sem where
  "partial_sem (Some C) S = sem C S"
| "partial_sem None S = S"

definition sem_lifted :: "'a hyper_program \<Rightarrow> 'a hyper_set \<Rightarrow> 'a hyper_set" where
  "sem_lifted Cs Ss i = partial_sem (Cs i) (Ss i)"


definition relational_hyper_hoare_triple
:: "'a rel_hyper_assertion \<Rightarrow> 'a hyper_program \<Rightarrow> 'a rel_hyper_assertion \<Rightarrow> bool"

 ("\<Turnstile> {_} [_] {_}" [51,0,0] 81) where
  "\<Turnstile> {P} [l] {Q} \<longleftrightarrow> (\<forall>S. P S \<longrightarrow> Q (sem_lifted l S))"

(*
List.map (\<lambda>p. sem (fst p) (snd p)) (zip l S)))"
*)

lemma relational_hyper_hoare_tripleI:
  assumes "\<And>S. P S \<Longrightarrow> Q (sem_lifted l S)"
  shows "\<Turnstile> {P} [l] {Q}"
  using assms relational_hyper_hoare_triple_def
  by blast

lemma relational_hyper_hoare_tripleE:
  assumes "\<Turnstile> {P} [l] {Q}"
      and "P S"
    shows "Q (sem_lifted l S)"
  by (meson assms(1) assms(2) relational_hyper_hoare_triple_def)


definition split_with_b :: "(nat, 'a) bexp \<Rightarrow> nat \<Rightarrow> 'a syn_assertion \<Rightarrow> 'a rel_hyper_assertion"
  where
  "split_with_b b k P = conj (interp_assert (split k P)) (\<lambda>S. \<forall>\<phi> \<in> S k. b (snd \<phi>) \<and> (\<forall>\<phi> \<in> S (Suc k). \<not> b (snd \<phi>)))"

fun programs_if :: "'a hyper_program \<Rightarrow> (nat, 'a) stmt \<Rightarrow> (nat, 'a) stmt \<Rightarrow> 'a hyper_program"
  where
  "programs_if Cs C1 C2 0 = Some C1"
| "programs_if Cs C1 C2 (Suc 0) = Some C2"
| "programs_if Cs C1 C2 (Suc (Suc n)) = Cs (Suc n)"


lemma set_filter_lnot:
  "S = Set.filter (b \<circ> snd) S \<union> Set.filter (lnot b \<circ> snd) S"
  apply rule
  unfolding lnot_def apply simp_all
   apply (simp add: subsetI)
  by (simp add: Set.filter_def)

(* Shift... ? *)
fun post_if_rel where
  "post_if_rel (AConst b) = AConst b"
| "post_if_rel (AComp e1 cmp e2) = AComp e1 cmp e2"
| "post_if_rel (AForallState 0 A) = AAnd (AForallState 0 (post_if_rel A)) (AForallState 1 (post_if_rel A))"
| "post_if_rel (AForallState (Suc n) A) = AForallState (Suc (Suc n)) (post_if_rel A)"
| "post_if_rel (AExistsState 0 A) = AOr (AExistsState 0 (post_if_rel A)) (AExistsState 1 (post_if_rel A))"
| "post_if_rel (AExistsState (Suc n) A) = AExistsState (Suc (Suc n)) (post_if_rel A)"
| "post_if_rel (AForall A) = AForall (post_if_rel A)"
| "post_if_rel (AExists A) = AExists (post_if_rel A)"
| "post_if_rel (AOr A B) = AOr (post_if_rel A) (post_if_rel B)"
| "post_if_rel (AAnd A B) = AAnd (post_if_rel A) (post_if_rel B)"

lemma post_if_rel_charact:
  assumes "is_split 0 old_sets new_sets" (* old_sets 0 = new_sets 0 \<union> new_sets 1 *)
      and "sat_assertion vals states (post_if_rel Q) new_sets"
    shows "sat_assertion vals states Q old_sets"
  using assms
proof (induct arbitrary: vals states rule: post_if_rel.induct)
  case (3 A)
  then show ?case
    apply (simp add: is_split_simpleE[OF 3(3)])
    using 3(1)[OF 3(3), of vals] by blast
next
  case (5 A)
  then show ?case
    apply (simp add: is_split_simpleE[OF 5(3)])
    using 5(1)[OF 5(3), of vals] by blast
qed (auto simp add: is_split_largerE)

fun split_first_set where
  "split_first_set b S 0 = Set.filter (b \<circ> snd) (S 0)"
| "split_first_set b S (Suc 0) = Set.filter (lnot b \<circ> snd) (S 0)"
| "split_first_set b S (Suc (Suc n)) = S (Suc n)"
  
lemma charact_split_first_set:
  assumes "Cs 0 = Some (if_then_else b C1 C2)"
  shows "is_split 0 (sem_lifted Cs S) (sem_lifted (programs_if Cs C1 C2) (split_first_set b S))"
  unfolding is_split_def sem_lifted_def apply simp
  apply (rule conjI)
   apply (simp add: assms assume_sem if_then_else_def sem_if sem_seq)
  by (metis Suc_lessD diff_Suc_Suc gr0_conv_Suc minus_nat.diff_0 programs_if.simps(3) split_first_set.simps(3) zero_less_diff)


lemma needed_for_soundness:
  assumes "interp_assert (post_if_rel Q) (sem_lifted (programs_if Cs C1 C2) (split_first_set b S))"
      and "Cs 0 = Some (if_then_else b C1 C2)"
    shows "interp_assert Q (sem_lifted Cs S)"
  using assms(1)
  apply (rule post_if_rel_charact[rotated])
  using assms(2) charact_split_first_set by blast



(*

\<turnstile> { split_with_b b 0 P } C1::C2::Cs {interp_assert (post_if_rel Q)}
-----------------------------------------------------------------------------
\<turnstile> { P } (if b C1 C2)::Cs {Q}

*)
theorem rule_if_relational:
  assumes "\<Turnstile> { split_with_b b 0 P } [ programs_if Cs C1 C2 ] {interp_assert (post_if_rel Q)}" (* Not Q here... *)
      and "Cs 0 = Some (if_then_else b C1 C2)"
  shows "\<Turnstile> { interp_assert P } [ Cs ] {interp_assert Q}"
proof (rule relational_hyper_hoare_tripleI)
  fix S assume asm0: "interp_assert P S"

  let ?S = "split_first_set b S"

  have "split_with_b b 0 P ?S"
    unfolding split_with_b_def conj_def apply simp_all
    apply (rule conjI)
     defer
     apply (simp add: lnot_def)
  proof -
    have "is_split 0 S ?S"
      unfolding is_split_def apply simp_all
      apply (rule conjI)
       apply (simp add: set_filter_lnot)
       apply (rule allI)
       apply (case_tac "i = 0")
        apply simp
       apply (case_tac "i = Suc 0")
       apply simp_all
      by (metis One_nat_def bot_nat_0.not_eq_extremum diff_Suc_1 split_first_set.elims)
    then show "interp_assert (split 0 P) ?S" using split_soundness[of 0 S ?S "[]" "[]" P]
      using asm0 by blast
  qed
  then have "interp_assert (post_if_rel Q) (sem_lifted (programs_if Cs C1 C2) ?S)"
    by (meson assms(1) relational_hyper_hoare_triple_def)
  then show "interp_assert Q (sem_lifted Cs S)"
    using assms(2) needed_for_soundness by blast
qed






section \<open>Extending (or Projecting)\<close>


lemma sem_lifted_on_disjoint_maps_seq:
  assumes "dom Cs \<inter> dom Cs' = {}"
  shows "sem_lifted (Cs ++ Cs') S = sem_lifted Cs' (sem_lifted Cs S)"
  unfolding sem_lifted_def
  by (metis (no_types, opaque_lifting) assms disjoint_insert(1) domIff insert_absorb map_add_dom_app_simps(1) map_add_dom_app_simps(3) partial_sem.simps(2))


theorem rel_extension:
  assumes "\<Turnstile> { P } [ Cs ] { R }"
      and "\<Turnstile> { R } [ Cs' ] { Q }"
      and "dom Cs \<inter> dom Cs' = {}"
    shows "\<Turnstile> { P } [ Cs ++ Cs' ] { Q }"
proof (rule relational_hyper_hoare_tripleI)
  fix S assume "P S"
  then show "Q (sem_lifted (Cs ++ Cs') S)"
    by (metis assms(1) assms(2) assms(3) relational_hyper_hoare_triple_def sem_lifted_on_disjoint_maps_seq)
qed




section \<open>Reindexing\<close>





type_synonym reindexing = "nat \<Rightarrow> nat"

fun reindex_syn_assertion where
  "reindex_syn_assertion \<pi> (AConst b) = AConst b"
| "reindex_syn_assertion \<pi> (AComp e1 cmp e2) = AComp e1 cmp e2"
| "reindex_syn_assertion \<pi> (AForallState n A) = AForallState (\<pi> n) (reindex_syn_assertion \<pi> A)"
| "reindex_syn_assertion \<pi> (AExistsState n A) = AExistsState (\<pi> n) (reindex_syn_assertion \<pi> A)"
| "reindex_syn_assertion \<pi> (AForall A) = AForall (reindex_syn_assertion \<pi> A)"
| "reindex_syn_assertion \<pi> (AExists A) = AExists (reindex_syn_assertion \<pi> A)"
| "reindex_syn_assertion \<pi> (AOr A B) = AOr (reindex_syn_assertion \<pi> A) (reindex_syn_assertion \<pi> B)"
| "reindex_syn_assertion \<pi> (AAnd A B) = AAnd (reindex_syn_assertion \<pi> A) (reindex_syn_assertion \<pi> B)"

definition reindex_hyper_stuff where
  "reindex_hyper_stuff \<pi> S n = S (\<pi> n)"

lemma reindex_equiv:
  "sat_assertion vals states (reindex_syn_assertion \<pi> A) S \<longleftrightarrow> sat_assertion vals states A (reindex_hyper_stuff \<pi> S)"
  unfolding reindex_hyper_stuff_def
  by (induct A arbitrary: vals states) auto

lemma reindex_both_impl:
  "sat_assertion vals states (reindex_syn_assertion \<pi> A) S \<Longrightarrow> sat_assertion vals states A (reindex_hyper_stuff \<pi> S)"
  "sat_assertion vals states A (reindex_hyper_stuff \<pi> S) \<Longrightarrow> sat_assertion vals states (reindex_syn_assertion \<pi> A) S"
  using reindex_equiv by blast+

lemma sem_lifted_reindex:
  "reindex_hyper_stuff \<pi> (sem_lifted Cs S) = sem_lifted (reindex_hyper_stuff \<pi> Cs) (reindex_hyper_stuff \<pi> S)"
  apply (rule ext)
  by (simp add: reindex_hyper_stuff_def sem_lifted_def)


theorem reindex_rule_one_direction:
  assumes "\<Turnstile> { interp_assert P } [ reindex_hyper_stuff \<pi> Cs ] {interp_assert Q}"
  shows "\<Turnstile> { interp_assert (reindex_syn_assertion \<pi> P) } [ Cs ] {interp_assert (reindex_syn_assertion \<pi> Q)}"
proof (rule relational_hyper_hoare_tripleI)
  fix S assume "interp_assert (reindex_syn_assertion \<pi> P) S"
  then have "interp_assert P (reindex_hyper_stuff \<pi> S)"
    by (simp add: reindex_both_impl(1))
  then have "interp_assert Q (sem_lifted (reindex_hyper_stuff \<pi> Cs) (reindex_hyper_stuff \<pi> S))"
    by (meson assms relational_hyper_hoare_triple_def)
  then show "interp_assert (reindex_syn_assertion \<pi> Q) (sem_lifted Cs S)"
    by (simp add: reindex_both_impl(2) sem_lifted_reindex)
qed

lemma reindex_bij:
  assumes "bij \<pi>"
  shows "P = reindex_syn_assertion \<pi> (reindex_syn_assertion (inv \<pi>) P)"
  using assms
  apply (induct P) apply simp_all
  by (metis bij_inv_eq_iff)+


theorem reindex_rule_one_direction_bij:
  assumes "\<Turnstile> { interp_assert (reindex_syn_assertion \<pi> P) } [ reindex_hyper_stuff (inv \<pi>) Cs ] {interp_assert (reindex_syn_assertion \<pi> Q)}"
      and "bij \<pi>"
  shows "\<Turnstile> { interp_assert P } [ Cs ] {interp_assert Q }"
proof -
  have "interp_assert P = interp_assert (reindex_syn_assertion (inv \<pi>) (reindex_syn_assertion (inv (inv \<pi>)) P))"
    by (metis assms(2) bij_betw_inv_into reindex_bij)
  moreover have "interp_assert Q = interp_assert (reindex_syn_assertion (inv \<pi>) (reindex_syn_assertion (inv (inv \<pi>)) Q))"
    by (metis assms(2) bij_betw_inv_into reindex_bij)
  ultimately show ?thesis
    by (simp add: assms(1) assms(2) inv_inv_eq reindex_rule_one_direction)
qed




(*
theorem reindex_rule_other_direction:
  assumes "\<Turnstile> { interp_assert (reindex_syn_assertion \<pi> P) } [ Cs ] {interp_assert (reindex_syn_assertion \<pi> Q)}"
  shows "\<Turnstile> { interp_assert P } [ reindex_hyper_stuff \<pi> Cs ] {interp_assert Q }"
(* I think this one needs bijection *)
proof (rule relational_hyper_hoare_tripleI)
  fix S assume "interp_assert P S"


"interp_assert (reindex_syn_assertion \<pi> P) S"
  then have "interp_assert P (reindex_hyper_stuff \<pi> S)"
    by (simp add: reindex_both_impl(1))
  then have "interp_assert Q (sem_lifted (reindex_hyper_stuff \<pi> Cs) (reindex_hyper_stuff \<pi> S))"
    by (meson assms relational_hyper_hoare_triple_def)
  then show "interp_assert (reindex_syn_assertion \<pi> Q) (sem_lifted Cs S)"
    by (simp add: reindex_both_impl(2) sem_lifted_reindex)
qed
*)



(* Use case: Generalized if rule *)

(*
theorem rule_if_relational_generalized:
  assumes "\<Turnstile> { split_with_b b k P } [ programs_if Cs C1 C2 ] {interp_assert (post_if_rel Q)}" (* Not Q here... *)
      and "Cs k = Some (if_then_else b C1 C2)"
    shows "\<Turnstile> { interp_assert P } [ Cs ] {interp_assert Q}"
proof (rule reindex_rule_one_direction_bij)

  thm rule_if_relational[of b ]
*)




section \<open>Generalized Lockstep Seq\<close>

fun seq_opt where
  "seq_opt (Some C1) (Some C2) = Some (C1;; C2)"
| "seq_opt (Some C1) None = Some C1"
| "seq_opt None r = r"

definition hyper_seq where
  "hyper_seq Cs Cs' n = seq_opt (Cs n) (Cs' n)"

lemma sem_lifted_hyper_seq:
  "sem_lifted Cs' (sem_lifted Cs S) = sem_lifted (hyper_seq Cs Cs') S"
  unfolding sem_lifted_def hyper_seq_def
  apply (rule ext)
  apply (case_tac "Cs i"; case_tac "Cs' i")
     apply simp_all
  using sem_seq by blast

theorem lockstep_seq:
  assumes "\<Turnstile> { P } [ Cs ] { R }"
      and "\<Turnstile> { R } [ Cs' ] { Q }"
    shows "\<Turnstile> { P } [ hyper_seq Cs Cs' ] { Q }"
proof (rule relational_hyper_hoare_tripleI)
  fix S assume "P S"
  then have "R (sem_lifted Cs S)"
    by (meson assms(1) relational_hyper_hoare_triple_def)
  then have "Q (sem_lifted Cs' (sem_lifted Cs S))"
    by (meson assms(2) relational_hyper_hoare_triple_def)
  then show "Q (sem_lifted (hyper_seq Cs Cs') S)"
    by (simp add: sem_lifted_hyper_seq)
qed




subsection \<open>Assume rule\<close>

(* Do it for 0! *)

fun transform_assume :: "'a syn_assertion \<Rightarrow> 'a syn_assertion \<Rightarrow> 'a syn_assertion" where
  "transform_assume _ (AConst b) = AConst b"
| "transform_assume _ (AComp e1 cmp e2) = AComp e1 cmp e2"
| "transform_assume b (AForallState 0 A) = AForallState 0 (AImp b (transform_assume b A))"
| "transform_assume b (AExistsState 0 A) = AExistsState 0 (AAnd b (transform_assume b A))"
| "transform_assume b (AForallState n A) = AForallState n (transform_assume b A)"
| "transform_assume b (AExistsState n A) = AExistsState n (transform_assume b A)"
| "transform_assume b (AForall A) = AForall (transform_assume b A)"
| "transform_assume b (AExists A) = AExists (transform_assume b A)"
| "transform_assume b (AAnd A B) = AAnd (transform_assume b A) (transform_assume b B)"
| "transform_assume b (AOr A B) = AOr (transform_assume b A) (transform_assume b B)"


definition same_syn_sem :: "'a syn_assertion \<Rightarrow> ('a npstate \<Rightarrow> bool) \<Rightarrow> bool"
  where
  "same_syn_sem bsyn bsem \<longleftrightarrow>
  (\<forall>states vals S. length states > 0 \<longrightarrow> bsem (snd (hd states)) = sat_assertion vals states bsyn S)"

lemma same_syn_semI:
  assumes "\<And>states vals S. length states > 0 \<Longrightarrow> bsem (snd (hd states)) \<longleftrightarrow> sat_assertion vals states bsyn S"
  shows "same_syn_sem bsyn bsem"
  by (simp add: assms same_syn_sem_def)

fun map_zero where
  "map_zero f S 0 = f (S 0)"
| "map_zero _ S (Suc n) = S (Suc n)"

lemma transform_assume_valid:
  assumes "same_syn_sem bsyn bsem"
  shows "sat_assertion vals states A (map_zero (Set.filter (bsem \<circ> snd)) S)
  \<longleftrightarrow> sat_assertion vals states (transform_assume bsyn A) S"
proof (induct A arbitrary: vals states)
  case (AForallState i A)
  let ?S = "map_zero (Set.filter (bsem \<circ> snd)) S"
  let ?A = "transform_assume bsyn A"
  have "sat_assertion vals states (AForallState i A) ?S \<longleftrightarrow> (\<forall>\<phi>\<in>?S i. sat_assertion vals (\<phi> # states) A ?S)"
    by force
  also have "... \<longleftrightarrow> (\<forall>\<phi>\<in>?S i. sat_assertion vals (\<phi> # states) ?A S)"
    using AForallState by presburger
  finally show ?case
  proof (cases i)
    case 0
    then have "(\<forall>\<phi>\<in>?S i. sat_assertion vals (\<phi> # states) ?A S) \<longleftrightarrow> (\<forall>\<phi>\<in>S i. bsem (snd \<phi>) \<longrightarrow> sat_assertion vals (\<phi> # states) ?A S)" 
      by fastforce
    also have "... \<longleftrightarrow> (\<forall>\<phi>\<in>S i. sat_assertion vals (\<phi> # states) bsyn S \<longrightarrow> sat_assertion vals (\<phi> # states) ?A S)"
      using assms same_syn_sem_def[of bsyn bsem] by auto
    also have "... \<longleftrightarrow> (\<forall>\<phi>\<in>S i. sat_assertion vals (\<phi> # states) (AImp bsyn ?A) S)"
      using sat_assertion_Imp by fast
    also have "... \<longleftrightarrow> sat_assertion vals states (AForallState i (AImp bsyn ?A)) S"
      using sat_assertion.simps(2) by force
    finally show ?thesis
      using transform_assume.simps(1)
      using "0" AForallState by force
  next
    case (Suc k)
    then show ?thesis
      by (metis (mono_tags, lifting) \<open>(\<forall>\<phi>\<in>map_zero (Set.filter (bsem \<circ> snd)) S i. sat_assertion vals (\<phi> # states) A (map_zero (Set.filter (bsem \<circ> snd)) S)) = (\<forall>\<phi>\<in>map_zero (Set.filter (bsem \<circ> snd)) S i. sat_assertion vals (\<phi> # states) (transform_assume bsyn A) S)\<close> map_zero.simps(2) sat_assertion.simps(3) transform_assume.simps(5))
  qed
next
  case (AExistsState i A)
  let ?S = "map_zero (Set.filter (bsem \<circ> snd)) S"
  let ?A = "transform_assume bsyn A"
  have "sat_assertion vals states (AExistsState i A) ?S \<longleftrightarrow> (\<exists>\<phi>\<in>?S i. sat_assertion vals (\<phi> # states) A ?S)"
    by force
  also have "... \<longleftrightarrow> (\<exists>\<phi>\<in>?S i. sat_assertion vals (\<phi> # states) ?A S)"
    using AExistsState by presburger
  then show ?case
  proof (cases i)
    case 0
    then have "(\<exists>\<phi>\<in>?S i. sat_assertion vals (\<phi> # states) ?A S) \<longleftrightarrow> (\<exists>\<phi>\<in>S i. bsem (snd \<phi>) \<and> sat_assertion vals (\<phi> # states) ?A S)"
      by force
    also have "... \<longleftrightarrow> (\<exists>\<phi>\<in>S i. sat_assertion vals (\<phi> # states) bsyn S \<and> sat_assertion vals (\<phi> # states) ?A S)"
      using assms same_syn_sem_def[of bsyn bsem] by auto
    also have "... \<longleftrightarrow> (\<exists>\<phi>\<in>S i. sat_assertion vals (\<phi> # states) (AAnd bsyn ?A) S)"
      by simp
    also have "... \<longleftrightarrow> sat_assertion vals states (AExistsState i (AAnd bsyn ?A)) S"
      using sat_assertion.simps(3) by force
    then show ?thesis
      by (metis "0" \<open>(\<exists>\<phi>\<in>map_zero (Set.filter (bsem \<circ> snd)) S i. sat_assertion vals (\<phi> # states) A (map_zero (Set.filter (bsem \<circ> snd)) S)) = (\<exists>\<phi>\<in>map_zero (Set.filter (bsem \<circ> snd)) S i. sat_assertion vals (\<phi> # states) (transform_assume bsyn A) S)\<close> \<open>sat_assertion vals states (AExistsState i A) (map_zero (Set.filter (bsem \<circ> snd)) S) = (\<exists>\<phi>\<in>map_zero (Set.filter (bsem \<circ> snd)) S i. sat_assertion vals (\<phi> # states) A (map_zero (Set.filter (bsem \<circ> snd)) S))\<close> calculation transform_assume.simps(4))
  next
    case (Suc k)
    then show ?thesis
      using AExistsState by auto
  qed
next
  case (AForall A)
  let ?S = "map_zero (Set.filter (bsem \<circ> snd)) S"
  let ?A = "transform_assume bsyn A"
  have "sat_assertion vals states (AForall A) ?S \<longleftrightarrow> (\<forall>v. sat_assertion (v # vals) states A ?S)"
    by force
  also have "... \<longleftrightarrow> (\<forall>v. sat_assertion (v # vals) states ?A S)"
    using AForall by presburger
  also have "... \<longleftrightarrow> sat_assertion vals states (AForall ?A) S"
    by simp
  then show ?case
    using calculation transform_assume.simps(3) by fastforce
next
  case (AExists A)
  let ?S = "map_zero (Set.filter (bsem \<circ> snd)) S"
  let ?A = "transform_assume bsyn A"
  have "sat_assertion vals states (AExists A) ?S \<longleftrightarrow> (\<exists>v. sat_assertion (v # vals) states A ?S)"
    by force
  also have "... \<longleftrightarrow> (\<exists>v. sat_assertion (v # vals) states ?A S)"
    using AExists by presburger
  also have "... \<longleftrightarrow> sat_assertion vals states (AExists ?A) S"
    by simp
  then show ?case
    using calculation transform_assume.simps(4) by fastforce
qed (simp_all)






subsubsection \<open>Program expressions (values)\<close>

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


subsubsection \<open>Program expressions (booleans)\<close>

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

lemma pexp_to_exp_same:
  shows "same_syn_sem (pbexp_to_assertion 0 pb) (interp_pbexp pb)"
proof (rule same_syn_semI)
  fix states :: "'a nstate list"
  fix vals S
  assume "0 < length states"
  then have "sat_assertion vals states (pbexp_to_assertion 0 pb) S = sat_assertion [] states (pbexp_to_assertion 0 pb) S"
    using same_syn_sem_assertion by blast
  then show "interp_pbexp pb (snd (hd states)) = sat_assertion vals states (pbexp_to_assertion 0 pb) S"
    by (metis \<open>0 < length states\<close> hd_conv_nth length_greater_0_conv same_syn_sem_assertion)
qed


lemma sem_lifted_map_zero:
  "sem_lifted [0 \<mapsto> C] S = map_zero (sem C) S"
  unfolding sem_lifted_def
  apply (rule ext)
  by (case_tac i) simp_all

subsubsection \<open>Syntactic rule for assume\<close>

theorem rule_assume_syntactic_general:
  "\<Turnstile> { sat_assertion vals states (transform_assume (pbexp_to_assertion 0 pb) P) } [ [0 \<mapsto> Assume (interp_pbexp pb)] ] {sat_assertion vals states P}"
proof (rule relational_hyper_hoare_tripleI)
  fix S assume asm0: "sat_assertion vals states (transform_assume (pbexp_to_assertion 0 pb) P) S"
  then have "sat_assertion vals states P (map_zero (Set.filter (interp_pbexp pb \<circ> snd)) S)"
    using pexp_to_exp_same transform_assume_valid by blast
  then show "sat_assertion vals states P (sem_lifted [0 \<mapsto> Assume (interp_pbexp pb)] S)"
  proof -
    have "\<forall>p r. sem (Assume p) (r::((nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a)) set) = Set.filter (p \<circ> snd) r"
      using assume_sem by blast
    then have "sat_assertion vals states P (map_zero (sem (Assume (interp_pbexp pb))) S)"
      using \<open>sat_assertion vals states P (map_zero (Set.filter (interp_pbexp pb \<circ> snd)) S)\<close> by presburger
    then show ?thesis by (simp add: sem_lifted_map_zero)
  qed
qed



theorem rule_assume_syntactic:
  "\<Turnstile> { interp_assert (transform_assume (pbexp_to_assertion 0 pb) P) } [ [0 \<mapsto> Assume (interp_pbexp pb)] ] {interp_assert P}"
  by (simp add: rule_assume_syntactic_general)






section \<open>Progress only one\<close>

corollary progress_any:
  assumes "Cs i = Some (C1;; C2)"
      and "\<Turnstile> {P} [ [i \<mapsto> C1] ] {R}"
      and "\<Turnstile> {R} [ Cs(i \<mapsto> C2) ] {Q}"
    shows "\<Turnstile> {P} [ Cs ] {Q}"
proof (rule relational_hyper_hoare_tripleI)
  fix S assume "P S"
  moreover have "Cs = hyper_seq [i \<mapsto> C1] (Cs(i \<mapsto> C2))"
    unfolding hyper_seq_def
    apply (rule ext)
    apply (case_tac "n = i")
    by (simp_all add: assms)
  ultimately show "Q (sem_lifted Cs S)"
    using lockstep_seq[of P "[i \<mapsto> C1]" R "Cs(i \<mapsto> C2)" Q]
    by (metis assms(2) assms(3) relational_hyper_hoare_triple_def)
qed



subsection \<open>Havoc rule\<close>

subsubsection \<open>Shifting variables\<close>

fun insert_at where
  "insert_at 0 x l = x # l"
| "insert_at (Suc n) x (t # q) = t # (insert_at n x q)"
| "insert_at (Suc n) x [] = [x]"

lemma length_insert_at:
  "length (insert_at n x l) = length l + 1"
proof (induct n arbitrary: l)
  case (Suc n)
  then show ?case
  proof (cases l)
    case (Cons t q)
    then show ?thesis
      by (simp add: Suc)
  qed (simp)
qed (simp_all)


lemma insert_at_charact_1:
  "n \<le> length l \<Longrightarrow> k < n \<Longrightarrow> (insert_at n x l) ! k = l ! k"
proof (induct k arbitrary: l n)
  case 0
  then show ?case
    by (metis bot_nat_0.not_eq_extremum insert_at.elims le_zero_eq list.size(3) nth_Cons_0)
next
  case (Suc k)
  then obtain nn t q where "n = Suc nn" "l = t # q"
    by (metis Suc_less_eq2 le_antisym list.exhaust list.size(3) not_less_zero zero_le)
  then show ?case
    using Suc.hyps Suc.prems(1) Suc.prems(2) by force
qed

lemma insert_at_charact_2:
  "n  \<le> length l \<Longrightarrow> (insert_at n x l) ! n = x"
proof (induct n arbitrary: l)
  case (Suc n)
  then show ?case
    by (metis Suc_le_length_iff insert_at.simps(2) nth_Cons_Suc)
qed (simp)

lemma insert_at_charact_3:
  "n  \<le> length l \<Longrightarrow> k \<ge> n \<Longrightarrow> (insert_at n x l) ! (Suc k) = l ! k"
proof (induct n arbitrary: l k)
  case (Suc xa)
  then obtain t q kk where "k = Suc kk" "l = t # q"
    by (meson Suc_le_D Suc_le_length_iff)
  then show ?case
    using Suc.hyps Suc.prems(1) Suc.prems(2) by auto
qed (simp)


(* Shift only stuff above *)
fun shift_vars_exp where
  "shift_vars_exp n (EQVar x) = (if x \<ge> n then EQVar (Suc x) else EQVar x)"
| "shift_vars_exp n (EBinop e1 op e2) = EBinop (shift_vars_exp n e1) op (shift_vars_exp n e2)"
| "shift_vars_exp n (EFun p e) = EFun p (shift_vars_exp n e)"
| "shift_vars_exp _ e = e"

fun shift_states_exp where
  "shift_states_exp n (EPVar \<phi> x) = (if \<phi> \<ge> n then EPVar (Suc \<phi>) x else EPVar \<phi> x)"
| "shift_states_exp n (ELVar \<phi> x) = (if \<phi> \<ge> n then ELVar (Suc \<phi>) x else ELVar \<phi> x)"
| "shift_states_exp n (EBinop e1 op e2) = EBinop (shift_states_exp n e1) op (shift_states_exp n e2)"
| "shift_states_exp n (EFun p e) = EFun p (shift_states_exp n e)"
| "shift_states_exp _ e = e"

fun wf_exp :: "nat \<Rightarrow> nat \<Rightarrow> 'a exp \<Rightarrow> bool" where
  "wf_exp nv ns (EPVar st _) \<longleftrightarrow> st < ns"
| "wf_exp nv ns (ELVar st _) \<longleftrightarrow> st < ns"
| "wf_exp nv ns (EQVar x) \<longleftrightarrow> x < nv"
| "wf_exp nv ns (EBinop e1 _ e2) \<longleftrightarrow> wf_exp nv ns e1 \<and> wf_exp nv ns e2"
| "wf_exp nv ns (EFun f e) \<longleftrightarrow> wf_exp nv ns e"
| "wf_exp nv ns (EConst _) \<longleftrightarrow> True"

lemma wf_shift_vars_exp:
  assumes "wf_exp nv ns e"
  shows "wf_exp (Suc nv) ns (shift_vars_exp n e)"
  using assms
  by (induct e) simp_all

lemma wf_shift_states_exp:
  assumes "wf_exp nv ns e"
  shows "wf_exp nv (Suc ns) (shift_states_exp n e)"
  using assms
  by (induct e) simp_all

lemma shift_vars_exp_charact:
  assumes "n \<le> length vals"
  shows "interp_exp vals states e = interp_exp (insert_at n v vals) states (shift_vars_exp n e)"
  using assms
proof (induct e)
  case (EQVar x)
  then show ?case
    by (simp add: insert_at_charact_1 insert_at_charact_3)
qed (simp_all)

lemma shift_states_exp_charact:
  assumes "n \<le> length states"
  shows "interp_exp vals states e = interp_exp vals (insert_at n \<phi> states) (shift_states_exp n e)"
  using assms
proof (induct e)
  case (EPVar x1 x2)
  then show ?case
    by (simp add: insert_at_charact_1 insert_at_charact_3)
next
  case (ELVar x1 x2)
  then show ?case
    by (simp add: insert_at_charact_1 insert_at_charact_3)
qed (simp_all)


fun shift_vars where
  "shift_vars n (AConst b) = AConst b"
| "shift_vars n (AComp e1 cmp e2) = AComp (shift_vars_exp n e1) cmp (shift_vars_exp n e2)"
| "shift_vars n (AForall A) = AForall (shift_vars (Suc n) A)"
| "shift_vars n (AExists A) = AExists (shift_vars (Suc n) A)"
| "shift_vars n (AForallState i A) = AForallState i (shift_vars n A)"
| "shift_vars n (AExistsState i A) = AExistsState i (shift_vars n A)"
| "shift_vars n (AOr A B) = AOr (shift_vars n A) (shift_vars n B)"
| "shift_vars n (AAnd A B) = AAnd (shift_vars n A) (shift_vars n B)"

lemma shift_vars_charact:
  assumes "n \<le> length vals"
  shows "sat_assertion vals states A S \<longleftrightarrow> sat_assertion (insert_at n x vals) states (shift_vars n A) S"
  using assms
proof (induct A arbitrary: vals states n)
  case (AComp x1a x2 x3a)
  then show ?case
    using shift_vars_exp_charact by fastforce
next
  case (AForall A)
  have "sat_assertion vals states (AForall A) S \<longleftrightarrow> (\<forall>v. sat_assertion (v # vals) states A S)"
    by simp
  also have "... \<longleftrightarrow> (\<forall>v. sat_assertion (insert_at (Suc n) x (v # vals)) states (shift_vars (Suc n) A) S)"
    using AForall(2) AForall(1)[of "Suc n" _ states] by simp
  also have "... \<longleftrightarrow> (\<forall>v. sat_assertion (v # insert_at n x vals) states (shift_vars (Suc n) A) S)"
    by simp
  also have "... \<longleftrightarrow> sat_assertion (insert_at n x vals) states (AForall (shift_vars (Suc n) A)) S"
    by simp
  then show "sat_assertion vals states (AForall A) S = sat_assertion (insert_at n x vals) states (shift_vars n (AForall A)) S"
    using calculation by simp
next
  case (AExists A)
  have "sat_assertion vals states (AExists A) S \<longleftrightarrow> (\<exists>v. sat_assertion (v # vals) states A S)"
    by simp
  also have "... \<longleftrightarrow> (\<exists>v. sat_assertion (insert_at (Suc n) x (v # vals)) states (shift_vars (Suc n) A) S)"
    using AExists(2) AExists(1)[of "Suc n" _ states] by simp
  also have "... \<longleftrightarrow> (\<exists>v. sat_assertion (v # insert_at n x vals) states (shift_vars (Suc n) A) S)"
    by simp
  also have "... \<longleftrightarrow> sat_assertion (insert_at n x vals) states (AExists (shift_vars (Suc n) A)) S"
    by simp
  then show "sat_assertion vals states (AExists A) S = sat_assertion (insert_at n x vals) states (shift_vars n (AExists A)) S"
    using calculation by simp
qed (simp_all)



subsubsection \<open>Expressions (Boolean and values)\<close>

definition update_state where
  "update_state \<phi> x v = (fst \<phi>, (snd \<phi>)(x := v))"


(* Replacing \<phi>(x) by v *)
(* for havoc, should be used with (EQVar v) *)
fun subst_exp_single :: "qstate \<Rightarrow> var \<Rightarrow> 'a exp \<Rightarrow> 'a exp \<Rightarrow> 'a exp" where
  "subst_exp_single \<phi> x e' (EPVar st y) = (if \<phi> = st \<and> x = y then e' else EPVar st y)"
| "subst_exp_single \<phi> x e' (EBinop e1 bop e2) = EBinop (subst_exp_single \<phi> x e' e1) bop (subst_exp_single \<phi> x e' e2)"
| "subst_exp_single \<phi> x e' (EFun f e) = EFun f (subst_exp_single \<phi> x e' e)"
| "subst_exp_single _ _ _ e = e" (* Logical variables, quantified variables, constants *)

lemma wf_subst_exp:
  assumes "wf_exp nv ns e"
      and "wf_exp nv ns e'"
    shows "wf_exp nv ns (subst_exp_single \<phi> x e' e)"
  using assms
  by (induct e) simp_all



lemma subst_exp_single_charact:
  assumes "interp_exp vals states e' = snd (states ! st) x"
  shows "interp_exp vals states (subst_exp_single st x e' e) = interp_exp vals states e"
  using assms
  by (induct e) simp_all


definition subst_state where
  "subst_state x pe \<phi> = (fst \<phi>, (snd \<phi>)(x := interp_pexp pe (snd \<phi>)))"

definition update_state_at where
  "update_state_at states n x v = list_update states n (update_state (states ! n) x v)"

lemma update_state_at_fst:
  "fst (update_state_at states n x v ! st) = fst (states ! st)"
proof (cases "n = st")
  case True
  then show ?thesis
    by (metis fst_conv linorder_not_less list_update_beyond nth_list_update_eq update_state_at_def update_state_def)
next
  case False
  then show ?thesis
    by (simp add: update_state_at_def)
qed

lemma update_state_at_snd_1:
  "x \<noteq> y \<Longrightarrow> snd (update_state_at states n x v ! st) y = snd (states ! st) y"
  apply (cases "n = st")
   apply (metis fun_upd_other linorder_not_less list_update_beyond nth_list_update_eq snd_conv update_state_at_def update_state_def)
  by (simp add: update_state_at_def)

lemma update_state_at_snd_2:
  "st \<noteq> n \<Longrightarrow> snd (update_state_at states n x v ! st) y = snd (states ! st) y"
  by (simp add: update_state_at_def)

lemma update_state_at_snd_3:
  assumes "n < length states"
  shows "snd (update_state_at states n x v ! n) x = v"
  by (simp add: assms update_state_at_def update_state_def)

lemma subst_exp_more_complex_charact:
  assumes "states' = update_state_at states st x (interp_exp vals states e')"
      and "st < length states"
  shows "interp_exp vals states (subst_exp_single st x e' e) = interp_exp vals states' e"
  using assms
proof (induct e)
  case (EPVar \<phi> y)
  then show ?case
    by (metis interp_exp.simps(1) subst_exp_single.simps(1) update_state_at_snd_1 update_state_at_snd_2 update_state_at_snd_3)
next
  case (ELVar x1 x2)
  then show ?case
    by (simp add: update_state_at_fst)
qed (simp_all)


subsubsection \<open>Assertions\<close>

fun subst_assertion_single :: "qstate \<Rightarrow> var \<Rightarrow> 'a exp \<Rightarrow> 'a syn_assertion \<Rightarrow> 'a syn_assertion" where
  "subst_assertion_single st x e (AConst b) = AConst b"
| "subst_assertion_single st x e (AComp e1 cmp e2) = AComp (subst_exp_single st x e e1) cmp (subst_exp_single st x e e2)"
| "subst_assertion_single st x e (AForall A) = AForall (subst_assertion_single st x (shift_vars_exp 0 e) A)"
| "subst_assertion_single st x e (AExists A) = AExists (subst_assertion_single st x (shift_vars_exp 0 e) A)"
| "subst_assertion_single st x e (AOr A B) = AOr (subst_assertion_single st x e A) (subst_assertion_single st x e B)"
| "subst_assertion_single st x e (AAnd A B) = AAnd (subst_assertion_single st x e A) (subst_assertion_single st x e B)"
| "subst_assertion_single st x e (AForallState i A) = AForallState i (subst_assertion_single (Suc st) x (shift_states_exp 0 e) A)"
| "subst_assertion_single st x e (AExistsState i A) = AExistsState i (subst_assertion_single (Suc st) x (shift_states_exp 0 e) A)"

fun wf_assertion_aux :: "nat \<Rightarrow> nat \<Rightarrow> 'a syn_assertion \<Rightarrow> bool" where
  "wf_assertion_aux nv ns (AConst b) \<longleftrightarrow> True"
| "wf_assertion_aux nv ns (AComp e1 cmp e2) \<longleftrightarrow> wf_exp nv ns e1 \<and> wf_exp nv ns e2"
| "wf_assertion_aux nv ns (AAnd A B) \<longleftrightarrow> wf_assertion_aux nv ns A \<and> wf_assertion_aux nv ns B"
| "wf_assertion_aux nv ns (AOr A B) \<longleftrightarrow> wf_assertion_aux nv ns A \<and> wf_assertion_aux nv ns B"

| "wf_assertion_aux nv ns (AForall A) \<longleftrightarrow> wf_assertion_aux (Suc nv) ns A"
| "wf_assertion_aux nv ns (AExists A) \<longleftrightarrow> wf_assertion_aux (Suc nv) ns A"
| "wf_assertion_aux nv ns (AForallState _ A) \<longleftrightarrow> wf_assertion_aux nv (Suc ns) A"
| "wf_assertion_aux nv ns (AExistsState _ A) \<longleftrightarrow> wf_assertion_aux nv (Suc ns) A"


abbreviation wf_assertion where "wf_assertion \<equiv> wf_assertion_aux 0 0"


lemma wf_shift_vars:
  assumes "wf_assertion_aux nv ns A"
  shows "wf_assertion_aux (Suc nv) ns (shift_vars n A)"
  using assms
  by (induct A arbitrary: n nv ns) (simp_all add: wf_shift_vars_exp)

lemma wf_subst_assertion:
  assumes "wf_assertion_aux nv ns A"
      and "wf_exp nv ns e"
    shows "wf_assertion_aux nv ns (subst_assertion_single \<phi> x e A)"
  using assms
proof (induct A arbitrary: nv ns e \<phi>)
  case (AComp x1a x2 x3a)
  then show ?case
    by (simp add: wf_subst_exp)
qed (simp_all add: wf_shift_vars_exp wf_shift_states_exp)

lemma subst_assertion_single_charact:
  assumes "interp_exp vals states e = snd (states ! st) x"
  shows "sat_assertion vals states (subst_assertion_single st x e A) S \<longleftrightarrow> sat_assertion vals states A S"
  using assms
proof (induct A arbitrary: vals states st e)
  case (AForallState i A)
  have "sat_assertion vals states (AForallState i A) S \<longleftrightarrow> (\<forall>\<phi> \<in> S i. sat_assertion vals (\<phi> # states) A S)"
    by simp
  also have "... \<longleftrightarrow> (\<forall>\<phi> \<in> S i. sat_assertion vals (\<phi> # states) (subst_assertion_single (Suc st) x (shift_states_exp 0 e) A) S)"
    using AForallState(1)[of vals _ "shift_states_exp 0 e" "Suc st"] AForallState(2)
    by (metis insert_at.simps(1) nth_Cons_Suc shift_states_exp_charact zero_le)
  finally show ?case by simp
next
  case (AExistsState i A)
  have "sat_assertion vals states (AExistsState i A) S \<longleftrightarrow> (\<exists>\<phi> \<in> S i. sat_assertion vals (\<phi> # states) A S)"
    by simp
  also have "... \<longleftrightarrow> (\<exists>\<phi> \<in> S i. sat_assertion vals (\<phi> # states) (subst_assertion_single (Suc st) x (shift_states_exp 0 e) A) S)"
    by (metis AExistsState.hyps AExistsState.prems insert_at.simps(1) nth_Cons_Suc shift_states_exp_charact zero_le)
  finally show ?case by simp
next
  case (AForall A)
  have "sat_assertion vals states (AForall A) S \<longleftrightarrow> (\<forall>v. sat_assertion (v # vals) states A S)"
    by simp
  also have "... \<longleftrightarrow> (\<forall>v. sat_assertion (v # vals) states (subst_assertion_single st x (shift_vars_exp 0 e) A) S)"
    by (metis AForall.hyps AForall.prems insert_at.simps(1) shift_vars_exp_charact zero_le)
  finally show ?case
    by simp
next
  case (AExists A)
  have "sat_assertion vals states (AExists A) S \<longleftrightarrow> (\<exists>v. sat_assertion (v # vals) states A S)"
    by simp
  also have "... \<longleftrightarrow> (\<exists>v. sat_assertion (v # vals) states (subst_assertion_single st x (shift_vars_exp 0 e) A) S)"
    by (metis AExists.hyps AExists.prems insert_at.simps(1) shift_vars_exp_charact zero_le)
  finally show ?case
    by simp
next
  case (AComp e1 cmp e2)
  then show ?case
    using subst_exp_single_charact[of vals states e st x] by auto
qed (simp_all)



lemma update_state_at_cons:
  "update_state_at (\<phi> # states) (Suc n) x v = \<phi> # update_state_at states n x v"
  by (simp add: update_state_at_def)


lemma subst_assertion_single_charact_better:
  assumes "states' = update_state_at states st x (interp_exp vals states e)"
      and "st < length states"
    shows "sat_assertion vals states (subst_assertion_single st x e A) S \<longleftrightarrow> sat_assertion vals states' A S"
  using assms
proof (induct A arbitrary: vals states states' st e)
  case (AComp x1a x2 x3a)
  then show ?case
    by (simp add: subst_exp_more_complex_charact)
next
  case (AForallState i A)
  have "sat_assertion vals states (subst_assertion_single st x e (AForallState i A)) S
  \<longleftrightarrow> (\<forall>\<phi>\<in>S i. sat_assertion vals (update_state_at (\<phi> # states) (Suc st) x (interp_exp vals (\<phi> # states) (shift_states_exp 0 e))) A S)"
    by (simp add: AForallState.hyps AForallState.prems(2))
  also have "... \<longleftrightarrow> (\<forall>\<phi>\<in>S i. sat_assertion vals (\<phi> # update_state_at states st x (interp_exp vals states e)) A S)"
    by (metis update_state_at_cons insert_at.simps(1) shift_states_exp_charact zero_le)
  finally show "sat_assertion vals states (subst_assertion_single st x e (AForallState i A)) S = sat_assertion vals states' (AForallState i A) S"
    by (simp add: AForallState.prems(1))
next
  case (AExistsState i A)
  have "sat_assertion vals states (subst_assertion_single st x e (AExistsState i A)) S
  \<longleftrightarrow> (\<exists>\<phi>\<in>S i. sat_assertion vals (update_state_at (\<phi> # states) (Suc st) x (interp_exp vals (\<phi> # states) (shift_states_exp 0 e))) A S)"
    by (simp add: AExistsState.hyps AExistsState.prems(2))
  also have "... \<longleftrightarrow> (\<exists>\<phi>\<in>S i. sat_assertion vals (\<phi> # update_state_at states st x (interp_exp vals states e)) A S)"
    by (metis update_state_at_cons insert_at.simps(1) shift_states_exp_charact zero_le)
  finally show "sat_assertion vals states (subst_assertion_single st x e (AExistsState i A)) S = sat_assertion vals states' (AExistsState i A) S"
    by (simp add: AExistsState.prems(1))
next
  case (AForall A)
  have "sat_assertion vals states (subst_assertion_single st x e (AForall A)) S
  \<longleftrightarrow> (\<forall>v. sat_assertion (v # vals) states (subst_assertion_single st x (shift_vars_exp 0 e) A) S)"
    by (simp add: AForall.hyps AForall.prems(2))
  then show ?case
    by (metis AForall.hyps AForall.prems(1) AForall.prems(2) insert_at.simps(1) sat_assertion.simps(5) shift_vars_exp_charact zero_le)
next
  case (AExists A)
  have "sat_assertion vals states (subst_assertion_single st x e (AExists A)) S
  \<longleftrightarrow> (\<exists>v. sat_assertion (v # vals) states (subst_assertion_single st x (shift_vars_exp 0 e) A) S)"
    by (simp add: AExists.hyps AExists.prems(2))
  then show ?case
    by (metis AExists.hyps AExists.prems(1) AExists.prems(2) insert_at.simps(1) sat_assertion.simps(6) shift_vars_exp_charact zero_le)
qed (simp_all)


subsubsection \<open>Transformation for havoc\<close>


(* Only for i = 0 *)
fun transform_havoc where
  "transform_havoc x (AForallState 0 A) = AForallState 0 (AForall (subst_assertion_single 0 x (EQVar 0) (shift_vars 0 (transform_havoc x A))))"
| "transform_havoc x (AExistsState 0 A) = AExistsState 0 (AExists (subst_assertion_single 0 x (EQVar 0) (shift_vars 0 (transform_havoc x A))))"
| "transform_havoc x (AForallState (Suc n) A) = AForallState (Suc n) (transform_havoc x A)"
| "transform_havoc x (AExistsState (Suc n) A) = AExistsState (Suc n) (transform_havoc x A)"
| "transform_havoc x (AExists A) = AExists (transform_havoc x A)"
| "transform_havoc x (AForall A) = AForall (transform_havoc x A)"
| "transform_havoc x (AOr A B) = AOr (transform_havoc x A) (transform_havoc x B)"
| "transform_havoc x (AAnd A B) = AAnd (transform_havoc x A) (transform_havoc x B)"
| "transform_havoc x (AConst b) = AConst b"
| "transform_havoc x (AComp e1 cmp e2) = AComp e1 cmp e2"


lemma sem_havoc_bis:
  "sem (Havoc x) S = {(fst \<phi>, (snd \<phi>)(x := v)) |\<phi> v. \<phi> \<in> S}" (is "?A = ?B")
proof
  show "?B \<subseteq> ?A"
    using sem_havoc by fastforce
  show "?A \<subseteq> ?B"
  proof
    fix \<phi> assume "\<phi> \<in> ?A"
    then obtain l \<sigma> v where "\<phi> = (l, \<sigma>(x := v))" "(l, \<sigma>) \<in> S"
      by (metis in_sem prod.collapse single_sem_Havoc_elim)
    then show "\<phi> \<in> ?B"
      by auto
  qed
qed

lemma helper_update_state:
  "(v # vals) ! 0 = snd ((update_state \<phi> x v # states) ! 0) x"
  by (simp add: update_state_def)

lemma helper_S_update_states:
  assumes "S' = { update_state \<phi> x v |\<phi> v. \<phi> \<in> S}"
  shows "(\<forall>\<phi> \<in> S'. Q \<phi>) \<longleftrightarrow> (\<forall>\<phi> \<in> S. \<forall>v. Q (update_state \<phi> x v))"
proof
  show "\<forall>\<phi>\<in>S'. Q \<phi> \<Longrightarrow> \<forall>\<phi>\<in>S. \<forall>v. Q (update_state \<phi> x v)"
    using assms by blast
  show "\<forall>\<phi>\<in>S. \<forall>v. Q (update_state \<phi> x v) \<Longrightarrow> \<forall>\<phi>\<in>S'. Q \<phi>"
    using assms by force
qed

lemma helper_S_update_states_exists:
  assumes "S' = { update_state \<phi> x v |\<phi> v. \<phi> \<in> S}"
  shows "(\<exists>\<phi> \<in> S'. Q \<phi>) \<longleftrightarrow> (\<exists>\<phi> \<in> S. \<exists>v. Q (update_state \<phi> x v))"
proof
  show "\<exists>\<phi>\<in>S'. Q \<phi> \<Longrightarrow> \<exists>\<phi>\<in>S. \<exists>v. Q (update_state \<phi> x v)"
    using assms by force
  show "\<exists>\<phi>\<in>S. \<exists>v. Q (update_state \<phi> x v) \<Longrightarrow> \<exists>\<phi>\<in>S'. Q \<phi>"
    using assms by blast
qed


(* TODO: only update 0 *)

lemma equiv_havoc_transform:
  assumes "S' = map_zero (\<lambda>S. { update_state \<phi> x v |\<phi> v. \<phi> \<in> S}) S"
  shows "sat_assertion vals states P S' \<longleftrightarrow> sat_assertion vals states (transform_havoc x P) S"
proof (induct P arbitrary: vals states)
  case (AForallState i P)

  let ?PP = "shift_vars 0 (transform_havoc x P)"
  let ?P = "subst_assertion_single 0 x (EQVar 0) ?PP"

  have rr: "\<And>\<phi> v. sat_assertion (v # vals) (\<phi> # states) ?P S
   \<longleftrightarrow> sat_assertion (v # vals) (update_state \<phi> x v # states) ?P S"
  proof -
    fix \<phi> v
    have "sat_assertion (v # vals) (insert_at 0 \<phi> states) (subst_assertion_single 0 x (EQVar 0) (shift_vars 0 (transform_havoc x P))) S =
sat_assertion (v # vals) (insert_at 0 (update_state \<phi> x v) states) (subst_assertion_single 0 x (EQVar 0) (shift_vars 0 (transform_havoc x P))) S"
      by (metis (no_types, lifting) One_nat_def helper_update_state insert_at.simps(1) interp_exp.simps(3) length_insert_at list_update_code(2) nth_Cons_0 subst_assertion_single_charact subst_assertion_single_charact_better trans_less_add2 update_state_at_def zero_less_Suc)
    then show "sat_assertion (v # vals) (\<phi> # states) ?P S \<longleftrightarrow> sat_assertion (v # vals) (update_state \<phi> x v # states) ?P S"
      by simp
  qed
  show ?case
  proof (cases i)
    case 0

  then have "sat_assertion vals states (transform_havoc x (AForallState i P)) S \<longleftrightarrow> sat_assertion vals states (AForallState i (AForall ?P)) S"
    by simp
  also have "... \<longleftrightarrow> (\<forall>\<phi> \<in> S i. \<forall>v. sat_assertion (v # vals) (update_state \<phi> x v # states) ?P S)"
    using rr by simp
  also have "... \<longleftrightarrow> (\<forall>\<phi> \<in> S i. \<forall>v. sat_assertion (v # vals) (update_state \<phi> x v # states) ?PP S)"
    using rr subst_assertion_single_charact[of _ _ _ _ x ?PP S] helper_update_state
    by (metis interp_exp.simps(3))
  also have "... \<longleftrightarrow> (\<forall>\<phi> \<in> S i. \<forall>v. sat_assertion vals (update_state \<phi> x v # states) (transform_havoc x P) S)"
    by (metis insert_at.simps(1) le0 shift_vars_charact)
  also have "... \<longleftrightarrow> (\<forall>\<phi> \<in> S i. \<forall>v. sat_assertion vals (update_state \<phi> x v # states) P S')"
    using AForallState.hyps AForallState.prems by force
  also have "... \<longleftrightarrow> sat_assertion vals states (AForallState i P) S'"
    using helper_S_update_states[of "S' i" x "S i" "\<lambda>\<phi>. sat_assertion vals (\<phi> # states) P S'"] assms
    by (simp add: "0")
  then show ?thesis
    using calculation by blast
  next
    case (Suc k)
    then show ?thesis
      using AForallState assms by auto
  qed
next
  case (AExistsState i P)

  let ?PP = "shift_vars 0 (transform_havoc x P)"
  let ?P = "subst_assertion_single 0 x (EQVar 0) ?PP"

  have rr: "\<And>\<phi> v. sat_assertion (v # vals) (\<phi> # states) ?P S
   \<longleftrightarrow> sat_assertion (v # vals) (update_state \<phi> x v # states) ?P S"
  proof -
    fix \<phi> v
    have "sat_assertion (v # vals) (insert_at 0 \<phi> states) (subst_assertion_single 0 x (EQVar 0) (shift_vars 0 (transform_havoc x P))) S =
sat_assertion (v # vals) (insert_at 0 (update_state \<phi> x v) states) (subst_assertion_single 0 x (EQVar 0) (shift_vars 0 (transform_havoc x P))) S"
      by (metis (no_types, lifting) One_nat_def helper_update_state insert_at.simps(1) insert_at_charact_2 interp_exp.simps(3) length_insert_at list_update_code(2) subst_assertion_single_charact subst_assertion_single_charact_better trans_less_add2 update_state_at_def zero_le zero_less_Suc)
    then show "sat_assertion (v # vals) (\<phi> # states) ?P S \<longleftrightarrow> sat_assertion (v # vals) (update_state \<phi> x v # states) ?P S"
      by simp
  qed
  show ?case
  proof (cases i)
    case 0
    then have "sat_assertion vals states (transform_havoc x (AExistsState i P)) S \<longleftrightarrow> sat_assertion vals states (AExistsState i (AExists ?P)) S"
      by simp
    also have "... \<longleftrightarrow> (\<exists>\<phi> \<in> S i. \<exists>v. sat_assertion (v # vals) (update_state \<phi> x v # states) ?P S)"
      using rr by simp
    also have "... \<longleftrightarrow> (\<exists>\<phi> \<in> S i. \<exists>v. sat_assertion (v # vals) (update_state \<phi> x v # states) ?PP S)"
      by (metis helper_update_state interp_exp.simps(3) subst_assertion_single_charact)
    also have "... \<longleftrightarrow> (\<exists>\<phi> \<in> S i. \<exists>v. sat_assertion vals (update_state \<phi> x v # states) (transform_havoc x P) S)"
      by (metis insert_at.simps(1) le0 shift_vars_charact)
    also have "... \<longleftrightarrow> (\<exists>\<phi> \<in> S i. \<exists>v. sat_assertion vals (update_state \<phi> x v # states) P S')"
      using AExistsState.hyps AExistsState.prems by force
    also have "... \<longleftrightarrow> sat_assertion vals states (AExistsState i P) S'"
      using helper_S_update_states_exists[of "S' i" x "S i" "\<lambda>\<phi>. sat_assertion vals (\<phi> # states) P S'"] assms
      using "0" by auto
    then show ?thesis
      using calculation by blast
  next
    case (Suc k)
    then show ?thesis
      using AExistsState assms by auto
  qed
qed (simp_all)




subsubsection \<open>Syntactic rule for havoc\<close>

theorem rule_havoc_syntactic_general:
  "\<Turnstile> { sat_assertion states vals (transform_havoc x P) } [ [0 \<mapsto> Havoc x] ] {sat_assertion states vals P}"
proof (rule relational_hyper_hoare_tripleI)
  fix S assume asm0: "sat_assertion states vals (transform_havoc x P) S"
  let ?S = "map_zero (sem (Havoc x)) S"
  have "sat_assertion states vals P ?S \<longleftrightarrow> sat_assertion states vals (transform_havoc x P) S"
  proof (rule equiv_havoc_transform)
    show "map_zero (sem (Havoc x)) S = map_zero (\<lambda>S. {update_state \<phi> x v |\<phi> v. \<phi> \<in> S}) S"
      apply (rule ext)
      apply (case_tac xa)
       apply simp_all
      by (simp add: sem_havoc_bis update_state_def)
  qed
  then show "sat_assertion states vals P (sem_lifted [0 \<mapsto> Havoc x] S)"
    by (simp add: asm0 sem_lifted_map_zero)
qed


theorem rule_havoc_syntactic:
  "\<Turnstile> { interp_assert (transform_havoc x P) } [ [0 \<mapsto> Havoc x] ] {interp_assert P}"
  by (simp add: rule_havoc_syntactic_general)











subsection \<open>Assignment rule\<close>

subsubsection \<open>Program expressions\<close>

fun subst_pexp :: "var \<Rightarrow> 'a pexp \<Rightarrow> 'a pexp \<Rightarrow> 'a pexp" where
  "subst_pexp x e (PVar y) = (if x = y then e else PVar y)"
| "subst_pexp x e (PBinop p1 op p2) = PBinop (subst_pexp x e p1) op (subst_pexp x e p2)"
| "subst_pexp x e (PFun f p) = PFun f (subst_pexp x e p)"
| "subst_pexp _ _ e = e" (* Constants and quantified vars *)

lemma subst_pexp_charact:
  "interp_pexp (subst_pexp x e' e) \<sigma> = interp_pexp e (\<sigma>(x := interp_pexp e' \<sigma>))"
proof (induct e)
  case (PVar x)
  then show ?case
    by (metis fun_upd_apply interp_pexp.simps(1) subst_pexp.simps(1))
qed (simp_all)

fun subst_pbexp :: "var \<Rightarrow> 'a pexp \<Rightarrow> 'a pbexp \<Rightarrow> 'a pbexp" where
  "subst_pbexp x e (PBAnd pb1 pb2) = PBAnd (subst_pbexp x e pb1) (subst_pbexp x e pb2)"
| "subst_pbexp x e (PBOr pb1 pb2) = PBOr (subst_pbexp x e pb1) (subst_pbexp x e pb2)"
| "subst_pbexp x e (PBComp p1 cmp p2) = PBComp (subst_pexp x e p1) cmp (subst_pexp x e p2)"
| "subst_pbexp _ _ (PBConst b) = PBConst b"

lemma subst_pbexp_charact:
  "interp_pbexp (subst_pbexp x e pb) \<sigma> \<longleftrightarrow> interp_pbexp pb (\<sigma>(x := interp_pexp e \<sigma>))"
proof (induct pb)
  case (PBComp x1 x2 x3)
  then show ?case
    using interp_pbexp.simps(4) subst_pexp_charact
    by (metis subst_pbexp.simps(3))
qed (simp_all)


subsubsection \<open>Expressions (Boolean and values)\<close>


definition subst_all_states where
  "subst_all_states x pe states = map (subst_state x pe) states"

fun subst_exp :: "var \<Rightarrow> 'a pexp \<Rightarrow> 'a exp \<Rightarrow> 'a exp" where
  "subst_exp x pe (EPVar st y) = (if x = y then pexp_to_exp st pe else EPVar st y)"
| "subst_exp x pe (EBinop e1 bop e2) = EBinop (subst_exp x pe e1) bop (subst_exp x pe e2)"
| "subst_exp x pe (EFun f e) = EFun f (subst_exp x pe e)"
| "subst_exp _ _ e = e" (* Logical variables, quantified variables, constants *)


lemma subst_exp_charact_aux:
  "snd (subst_state x pe (states ! st)) x = interp_exp vals states (pexp_to_exp st pe)"
  by (induct pe) (simp_all add: subst_state_def)

lemma subst_exp_charact:
  assumes "wf_exp nv (length states) e"
    shows "interp_exp vals states (subst_exp x pe e) = interp_exp vals (subst_all_states x pe states) e"
  using assms
proof (induct e)
  case (EPVar st y)
  let ?states = "subst_all_states x pe states"
  have "snd (subst_state x pe (states ! st)) = snd (?states ! st)"
    by (metis EPVar.prems(1) nth_map subst_all_states_def wf_exp.simps(1))
  show "interp_exp vals states (subst_exp x pe (EPVar st y)) = interp_exp vals ?states (EPVar st y)"
  proof (cases "x = y")
    case True
    then have "interp_exp vals states (subst_exp x pe (EPVar st y)) = interp_exp vals states (pexp_to_exp st pe)"
      by simp
    moreover have "interp_exp vals ?states (EPVar st y) = snd (?states ! st) y"
      by simp
    moreover have "... = snd (subst_state x pe (states ! st)) y"
      by (simp add: \<open>snd (subst_state x pe (states ! st)) = snd (subst_all_states x pe states ! st)\<close>)
    moreover have "snd (subst_state x pe (states ! st)) x = interp_exp vals states (pexp_to_exp st pe)"
      by (metis subst_exp_charact_aux)
    ultimately show ?thesis
      using True by fastforce
  next
    case False
    then show ?thesis
      by (metis \<open>snd (subst_state x pe (states ! st)) = snd (subst_all_states x pe states ! st)\<close> fun_upd_other interp_exp.simps(1) snd_conv subst_exp.simps(1) subst_state_def)
  qed
next
  case (ELVar st y)
  let ?states = "subst_all_states x pe states"
  have "fst (states ! st) = fst (?states ! st)"
    by (metis ELVar.prems(1) fst_conv nth_map subst_all_states_def subst_state_def wf_exp.simps(2))
  have "interp_exp vals states (subst_exp x pe (ELVar st y)) = interp_exp vals states (ELVar st y)"
    by simp
  also have "... = fst (states ! st) y"
    by simp
  also have "... = fst (?states ! st) y"
    by (simp add: \<open>fst (states ! st) = fst (subst_all_states x pe states ! st)\<close>)
  also have "... = interp_exp vals ?states (ELVar st y)"
    by auto
  then show "interp_exp vals states (subst_exp x pe (ELVar st y)) = interp_exp vals ?states (ELVar st y)"
    using calculation by presburger
qed (simp_all)



subsubsection \<open>Assertions\<close>

(* only for 0 *)
fun transform_assign where
  "transform_assign x pe (AForallState 0 A) = AForallState 0 (subst_assertion_single 0 x (pexp_to_exp 0 pe) (transform_assign x pe A))"
| "transform_assign x pe (AExistsState 0 A) = AExistsState 0 (subst_assertion_single 0 x (pexp_to_exp 0 pe) (transform_assign x pe A))"
| "transform_assign x pe (AForallState (Suc n) A) = AForallState (Suc n) (transform_assign x pe A)"
| "transform_assign x pe (AExistsState (Suc n) A) = AExistsState (Suc n) (transform_assign x pe A)"
| "transform_assign x pe (AExists A) = AExists (transform_assign x pe A)"
| "transform_assign x pe (AForall A) = AForall (transform_assign x pe A)"
| "transform_assign x pe (AOr A B) = AOr (transform_assign x pe A) (transform_assign x pe B)"
| "transform_assign x pe (AAnd A B) = AAnd (transform_assign x pe A) (transform_assign x pe B)"
| "transform_assign x pe (AConst b) = AConst b"
| "transform_assign x pe (AComp e1 cmp e2) = AComp e1 cmp e2"


lemma transform_assign_works:
  "sat_assertion vals states (transform_assign x pe A) S = sat_assertion vals states A (map_zero (\<lambda>S. subst_state x pe ` S) S)"
proof (induct A arbitrary: vals states)
  case (AForallState i A)
  then show ?case
    apply (cases i)
     apply simp_all
    using subst_assertion_single_charact_better AForallState update_state_at_def
    list_update_code(2) nth_Cons_0 same_syn_sem_exp subst_state_def update_state_def
    by (metis length_greater_0_conv list.simps(3))
next
  case (AExistsState i A)
  then show ?case
    apply (cases i)
     apply simp_all
    using subst_assertion_single_charact_better AExistsState update_state_at_def
    list_update_code(2) nth_Cons_0 same_syn_sem_exp subst_state_def update_state_def
    by (metis length_greater_0_conv list.simps(3))
qed (simp_all)


subsubsection \<open>Syntactic rule for assignments\<close>

lemma subst_state_equiv_def:
  "{(l, \<sigma>(x := interp_pexp pe \<sigma>)) |l \<sigma>. (l, \<sigma>) \<in> S} = subst_state x pe ` S" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof
    fix \<phi> assume "\<phi> \<in> ?A"
    then obtain l \<sigma> where "\<phi> = (l, \<sigma>(x := interp_pexp pe \<sigma>))" "(l, \<sigma>) \<in> S"
      by blast
    then show "\<phi> \<in> ?B"
      by (metis (mono_tags, lifting) fst_conv image_iff snd_conv subst_state_def)
  qed
  show "?B \<subseteq> ?A"
    using subst_state_def by fastforce
qed


theorem rule_assign_syntactic_general:
  "\<Turnstile> { sat_assertion vals states (transform_assign x pe P) } [ [0 \<mapsto> Assign x (interp_pexp pe)] ] {sat_assertion vals states P}"
  apply (rule relational_hyper_hoare_tripleI)
  using transform_assign_works[of vals states x pe P] subst_state_equiv_def[of x pe]
proof -
  fix S :: "nat \<Rightarrow> ((nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a)) set"
  assume "sat_assertion vals states (transform_assign x pe P) S"
  then have f1: "sat_assertion vals states P (map_zero ((`) (subst_state x pe)) S)"
    using \<open>\<And>S. sat_assertion vals states (transform_assign x pe P) S = sat_assertion vals states P (map_zero ((`) (subst_state x pe)) S)\<close> by blast
  have "\<forall>r. sem (Assign x (interp_pexp pe)) (r::((nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a)) set) = subst_state x pe ` r"
    by (simp add: \<open>\<And>S. {(l, \<sigma>(x := interp_pexp pe \<sigma>)) |l \<sigma>. (l, \<sigma>) \<in> S} = subst_state x pe ` S\<close> sem_assign)
  then have "sat_assertion vals states P (map_zero (sem (Assign x (interp_pexp pe))) S)"
    using f1 by presburger
  then show "sat_assertion vals states P (sem_lifted [0 \<mapsto> Assign x (interp_pexp pe)] S)"
    by (simp add: sem_lifted_map_zero)
qed



theorem rule_assign_syntactic:
  "\<Turnstile> { interp_assert (transform_assign x pe P) } [ [0 \<mapsto> Assign x (interp_pexp pe)] ] {interp_assert P}"
  by (simp add: rule_assign_syntactic_general)





subsection \<open>Thibault's Loop rules\<close>


fun no_exists_stateI :: "nat set \<Rightarrow> 'a syn_assertion \<Rightarrow> bool"
  where
  "no_exists_stateI I (AConst _) \<longleftrightarrow> True"
| "no_exists_stateI I (AComp _ _ _) \<longleftrightarrow> True"
| "no_exists_stateI I (AForallState _ A) \<longleftrightarrow> no_exists_stateI I A"
| "no_exists_stateI I (AExistsState i A) \<longleftrightarrow> i \<notin> I \<and> no_exists_stateI I A"
| "no_exists_stateI I (AForall A) \<longleftrightarrow> no_exists_stateI I A"
| "no_exists_stateI I (AExists A) \<longleftrightarrow> no_exists_stateI I A"
| "no_exists_stateI I (AAnd A B) \<longleftrightarrow> no_exists_stateI I A \<and> no_exists_stateI I B"
| "no_exists_stateI I (AOr A B) \<longleftrightarrow> no_exists_stateI I A \<and> no_exists_stateI I B"

definition hyper_set_le where
  "hyper_set_le I S S' \<longleftrightarrow> (\<forall>i\<in>I. S i \<subseteq> S' i) \<and> (\<forall>i. i \<notin> I \<longrightarrow> S i = S' i)"

lemma hyper_set_leI:
  assumes "\<And>i. i \<in> I \<Longrightarrow> S i \<subseteq> S' i"
      and "\<And>i. i \<notin> I \<Longrightarrow> S i = S' i"
    shows "hyper_set_le I S S'"
  by (simp add: assms(1) assms(2) hyper_set_le_def)

lemma mono_sym_then_up_closed:
  assumes "no_exists_stateI I A"
      and "hyper_set_le I S S'"
      and "sat_assertion vals states A S'"
    shows "sat_assertion vals states A S"
  using assms
proof (induct A arbitrary: vals states)
  case (AForallState i A)
  then have "S i \<subseteq> S' i"
    by (metis Orderings.order_eq_iff hyper_set_le_def)
  then show ?case
    using AForallState.hyps AForallState.prems(1) AForallState.prems(3) assms(2) by auto
next
  case (AExistsState i A)
  then show ?case
  proof (simp)
    obtain \<phi> where "\<phi>\<in>S i" "sat_assertion vals (\<phi> # states) A S'"
      using AExistsState(3) unfolding hyper_set_le_def
      using AExistsState.prems(1) AExistsState.prems(3) by auto
    then have "sat_assertion vals (\<phi> # states) A S"
      using AExistsState(1)[OF _ AExistsState(3), of vals "\<phi> # states"]
      using AExistsState.prems(1) by fastforce
    then show "\<exists>\<phi>\<in>S i. sat_assertion vals (\<phi> # states) A S"
      using \<open>\<phi> \<in> S i\<close> by blast
  qed
qed (auto)





section \<open>General while loop from Thibault\<close>


(* Set becomes larger for  *)
definition hyper_ascending :: "nat set \<Rightarrow> (nat \<Rightarrow> 'a hyper_set) \<Rightarrow> bool" where
  "hyper_ascending I S \<longleftrightarrow> (\<forall>n m. n \<le> m \<longrightarrow> hyper_set_le I (S n) (S m))"

lemma hyper_ascendingI_direct:
  assumes "\<And>n m. n \<le> m \<Longrightarrow> hyper_set_le I (S n) (S m)"
  shows "hyper_ascending I S"
  by (simp add: hyper_ascending_def assms)

lemma hyper_set_le_trans:
  assumes "hyper_set_le I A B"
      and "hyper_set_le I B C"
    shows "hyper_set_le I A C"
  using assms unfolding hyper_set_le_def
  by blast

lemma hyper_set_le_refl:
  "hyper_set_le I A A"
  unfolding hyper_set_le_def by blast

lemma hyper_ascendingI:
  assumes "\<And>n. hyper_set_le I (S n) (S (Suc n))"
  shows "hyper_ascending I S"
proof (rule hyper_ascendingI_direct)
  fix n m :: nat assume asm0: "n \<le> m"
  moreover have "n \<le> m \<Longrightarrow> hyper_set_le I (S n) (S m)"
  proof (induct "m - n" arbitrary: m n)
    case (Suc x)
    then show ?case
      by (metis (no_types, opaque_lifting) add_Suc_right assms diff_add_inverse diff_add_inverse2 diff_le_self hyper_set_le_trans ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
  qed (simp add: hyper_set_le_refl)
  ultimately show "hyper_set_le I (S n) (S m)" 
    by blast
qed

definition hyper_union where
  "hyper_union Ss i = (\<Union>n. Ss n i)"


definition relational_upwards_closed where
  "relational_upwards_closed I P P_inf \<longleftrightarrow> (\<forall>Ss. hyper_ascending I Ss \<and> (\<forall>n. P n (Ss n)) \<longrightarrow> P_inf (hyper_union Ss))"

lemma relational_upwards_closedI:
  assumes "\<And>S. hyper_ascending I S \<Longrightarrow> (\<forall>n. P n (S n)) \<Longrightarrow> P_inf (hyper_union S)"
  shows "relational_upwards_closed I P P_inf"
  by (simp add: assms relational_upwards_closed_def)

lemma upwards_closedE:
  assumes "relational_upwards_closed I P P_inf"
      and "hyper_ascending I S"
      and "\<And>n. P n (S n)"
    shows "P_inf (hyper_union S)"
  using assms(1) assms(2) assms(3) relational_upwards_closed_def by blast


definition construct_programs where
  "construct_programs I f i = (if i \<in> I then Some (f i) else None)"


definition holds_forall_relational where
  "holds_forall_relational I b S \<longleftrightarrow> (\<forall>i \<in> I. \<forall>\<phi>\<in>S i. b (snd \<phi>))"


fun iterate_sem_lifted where
  "iterate_sem_lifted 0 _ S = S"
| "iterate_sem_lifted (Suc n) Cs S = sem_lifted Cs (iterate_sem_lifted n Cs S)"

lemma relational_indexed_invariant_then_power:
  assumes "\<And>n. relational_hyper_hoare_triple (I n) Cs (I (Suc n))"
      and "I 0 S"
  shows "I n (iterate_sem_lifted n Cs S)"
  using assms
proof (induct n arbitrary: S)
next
  case (Suc n)
  then have "I n (iterate_sem_lifted n Cs S)"
    by blast
  then have "I (Suc n) (sem_lifted Cs (iterate_sem_lifted n Cs S))"
    using Suc.prems(1) relational_hyper_hoare_tripleE by blast
  then show ?case
    by (simp add: Suc.hyps Suc.prems(1))
qed (auto)

definition union_hyper_sets where
  "union_hyper_sets A B i = A i \<union> B i"

fun relational_union_up_to_n where
  "relational_union_up_to_n C S 0 = iterate_sem_lifted 0 C S"
| "relational_union_up_to_n C S (Suc n) = union_hyper_sets (iterate_sem_lifted (Suc n) C S) (relational_union_up_to_n C S n)"

definition map_indices where
  "map_indices I f S i = (if i \<in> I then f i (S i) else S i)"

definition filter_exp_indices where
  "filter_exp_indices I b S = map_indices I (\<lambda>i. filter_exp (lnot (b i))) S"

lemma relational_iterate_sem_assume_increasing:
  assumes "Cs = construct_programs I (\<lambda>i. if_then (b i) (C i))"
  shows "hyper_set_le I (filter_exp_indices I b (iterate_sem_lifted n Cs S)) (filter_exp_indices I b (iterate_sem_lifted (Suc n) Cs S))"
  apply (rule hyper_set_leI)
  using assms unfolding hyper_set_le_def filter_exp_indices_def construct_programs_def map_indices_def
   apply simp_all
   apply (smt (verit) UnCI filter_exp_def if_then_sem member_filter option.sel partial_sem.elims sem_lifted_def subsetI)
  by (simp add: sem_lifted_def)


lemma relational_filter_exp_union:
  "filter_exp_indices I b (union_hyper_sets S1 S2) = union_hyper_sets (filter_exp_indices I b S1) (filter_exp_indices I b S2)" (is "?A = ?B")
  unfolding filter_exp_indices_def union_hyper_sets_def
  apply (rule ext)
  apply rule
  by (simp_all add: filter_exp_union map_indices_def)


(*
lemma relational_iterate_sem_assume_increasing_union_up_to:
  assumes "Cs = construct_programs I (\<lambda>i. if_then (b i) (C i))"
  shows "filter_exp_indices I b (iterate_sem_lifted n Cs S) = filter_exp_indices I b (relational_union_up_to_n Cs S n)"


theorem relational_while_general_simple:
  assumes "\<And>n. \<Turnstile> {P n} [ construct_programs I (\<lambda>i. if_then (b i) (C i)) ] { P (Suc n) }"
      and "\<And>n. \<Turnstile> {P n} [ construct_programs I (\<lambda>i. Assume (lnot (b i))) ] {Q n}"
      and "relational_upwards_closed I Q Q_inf"

  shows "\<Turnstile> {P 0} [ construct_programs I (\<lambda>i. while_cond (b i) (C i)) ] {conj Q_inf (\<lambda>S. \<forall>i \<in> I. \<forall>\<phi> \<in> S i. \<not> b i (snd \<phi>)) }"

*)
(* Thibault's own TODO: Think about this: *)

lemma ascending_iterate_filter:
  "ascending (\<lambda>n. filter_exp (lnot b) (union_up_to_n (if_then b C) S n))"
  by (metis ascendingI iterate_sem_assume_increasing iterate_sem_assume_increasing_union_up_to)



section \<open>Consequence Rules\<close>

lemma precondition_conseq:
  assumes "entails P P'"
      and "\<Turnstile> {P'} [C] {Q}"
    shows "\<Turnstile> {P} [C] {Q}"
  by (metis (mono_tags, lifting) assms(1,2) entails_def relational_hyper_hoare_triple_def)

lemma postcondition_conseq:
  assumes "entails Q' Q"
      and "\<Turnstile> {P} [C] {Q'}"
    shows "\<Turnstile> {P} [C] {Q}"
  by (metis (mono_tags, lifting) assms(1,2) entails_def relational_hyper_hoare_triple_def)




section \<open>Rewrite Rule\<close>


definition sem_equiv_hyper where
"sem_equiv_hyper Cs1 Cs2 P \<longleftrightarrow> (\<forall>S. P S \<longrightarrow> (sem_lifted Cs1 S) = (sem_lifted Cs2 S))"


theorem rewrite_rule:
  assumes "sem_equiv_hyper Cs1 Cs2 P"
  shows "\<Turnstile> {P} [Cs1] {Q} \<longleftrightarrow> \<Turnstile> {P} [Cs2] {Q}"
  using assms
  by(auto simp add:relational_hyper_hoare_triple_def sem_lifted_def sem_equiv_hyper_def)

section \<open>If Lockstep\<close>

definition map_comprehension :: "('i \<Rightarrow> 'a) \<Rightarrow> ('i \<Rightarrow> bool) \<Rightarrow> ('i \<rightharpoonup> 'a)" where
  "map_comprehension f P \<equiv> (\<lambda>i. if P i then Some (f i) else None)"

translations
  "[i \<mapsto> t | P]" => "CONST map_comprehension (\<lambda>i. t) (\<lambda>i. P)"


lemma sem_lifted_rewrite: "sem_lifted [ i \<mapsto> (C i) | i \<in> I ] S = (\<lambda>i. if (i \<in> I) then (sem (C i) (S i)) else (S i))"
  by (metis (mono_tags, lifting) map_comprehension_def partial_sem.simps(1,2) sem_lifted_def) 

definition holds_forall_hyper where
  "holds_forall_hyper I bs S \<longleftrightarrow> (\<forall>i\<in>I. \<forall>\<phi>\<in>(S i). (bs i) (snd \<phi>))"

definition low_exp_hyper where
  "low_exp_hyper I es S = (\<forall>i\<in>I. \<forall>i'\<in>I. \<forall>\<phi> \<phi>'. (\<phi> \<in> (S i) \<and> \<phi>' \<in> (S i')) \<longrightarrow> ((es i) (snd \<phi>) = (es i') (snd \<phi>')))"

definition lnot_hyper where
  "lnot_hyper bs i \<sigma> = (\<not>(bs i) \<sigma>)"



theorem if_lockstep_true:
  assumes "\<Turnstile> { conj P (holds_forall_hyper I bs) } [[i \<mapsto> (Cs1 i) | i \<in> I]] { Q }"
    shows "\<Turnstile> { conj P (holds_forall_hyper I bs)} [[ i \<mapsto> (if_then_else (bs i) (Cs1 i) (Cs2 i)) | i \<in> I ]] { Q }"
proof -
  have "sem_equiv_hyper [i \<mapsto> (Cs1 i) | i \<in> I] [ i \<mapsto> (if_then_else (bs i) (Cs1 i) (Cs2 i)) | i \<in> I ] (conj P (holds_forall_hyper I bs))"
    apply(auto simp add:holds_forall_hyper_def sem_equiv_hyper_def conj_def snd_def sem_lifted_rewrite)
    apply(rule ext)
    apply(auto simp add:sem_def if_then_else_def lnot_def)
    apply (metis SemAssume SemIf1 SemSeq case_prod_conv)
    by auto
  with assms rewrite_rule show "\<Turnstile> { conj P (holds_forall_hyper I bs)} [[ i \<mapsto> (if_then_else (bs i) (Cs1 i) (Cs2 i)) | i \<in> I ]] { Q }" by auto
qed



theorem if_lockstep_true_sym:
  assumes "\<Turnstile> { conj P (holds_forall_hyper I bs)} [[ i \<mapsto> (if_then_else (bs i) (Cs1 i) (Cs2 i)) | i \<in> I ]] { Q }"
  shows "\<Turnstile> { conj P (holds_forall_hyper I bs) } [[i \<mapsto> (Cs1 i) | i \<in> I]] { Q }"
proof -
  have "sem_equiv_hyper [i \<mapsto> (Cs1 i) | i \<in> I] [ i \<mapsto> (if_then_else (bs i) (Cs1 i) (Cs2 i)) | i \<in> I ] (conj P (holds_forall_hyper I bs))"
    apply(auto simp add:holds_forall_hyper_def sem_equiv_hyper_def conj_def snd_def sem_lifted_rewrite)
    apply(rule ext)
    apply(auto simp add:sem_def if_then_else_def lnot_def)
    apply (metis SemAssume SemIf1 SemSeq case_prod_conv)
    by auto
  with assms rewrite_rule show "\<Turnstile> { conj P (holds_forall_hyper I bs) } [[i \<mapsto> (Cs1 i) | i \<in> I]] { Q }" by auto
qed


theorem if_lockstep_false:
  assumes "\<Turnstile> { conj P (holds_forall_hyper I (lnot_hyper bs)) } [[i \<mapsto> (Cs2 i) | i \<in> I]] { Q }"
    shows "\<Turnstile> { conj P (holds_forall_hyper I (lnot_hyper bs))} [[ i \<mapsto> (if_then_else (bs i) (Cs1 i) (Cs2 i)) | i \<in> I ]] { Q }"
proof -
  let ?bs' = "lnot_hyper bs"
  have eqv:"sem_equiv_hyper [i \<mapsto> (if_then_else (bs i) (Cs1 i) (Cs2 i)) | i \<in> I ] [ i \<mapsto> (if_then_else (?bs' i) (Cs2 i) (Cs1 i)) | i \<in> I ] (conj P (holds_forall_hyper I (lnot_hyper bs)))"
    apply(auto simp add:sem_equiv_hyper_def sem_lifted_rewrite)
    apply(rule ext)
    apply(auto simp add:sem_def if_then_else_def lnot_def lnot_hyper_def)
       apply (metis SemAssume SemIf2 SemSeq lnot_def lnot_hyper_def)
      apply (metis SemAssume SemIf1 SemSeq lnot_hyper_def)
     apply (metis SemAssume SemIf2 SemSeq lnot_def)
    by (meson SemAssume SemIf1 SemSeq)
  have "\<Turnstile> { conj P (holds_forall_hyper I ?bs')} [[ i \<mapsto> (if_then_else (?bs' i) (Cs2 i) (Cs1 i)) | i \<in> I ]] { Q }" 
    apply(rule if_lockstep_true)
    apply(auto simp add:assms)
    done
  with eqv rewrite_rule show "\<Turnstile> { conj P (holds_forall_hyper I (lnot_hyper bs))} [[ i \<mapsto> (if_then_else (bs i) (Cs1 i) (Cs2 i)) | i \<in> I ]] { Q }" by auto
qed

lemma low_exp_either: "(low_exp_hyper I bs) S \<Longrightarrow> (holds_forall_hyper I bs S) \<or> (holds_forall_hyper I (lnot_hyper bs) S)"
  by (smt (verit) holds_forall_hyper_def lnot_hyper_def low_exp_hyper_def)

lemma either_low_exp: "(holds_forall_hyper I bs S) \<or> (holds_forall_hyper I (lnot_hyper bs) S) \<Longrightarrow> low_exp_hyper I bs S"
  by (smt (verit, del_insts) holds_forall_hyper_def lnot_hyper_def low_exp_hyper_def)


text\<open> A rule to progress all if statements in a lockstep given all executions will either take the first branch
or will all take the second branch.
Rule based directly on if_synchronized from HHL which translates directly into IfSync rule from the paper.
Uses the combination of total functions and a set of indices I to represent partial functions.
\<close>
theorem if_lockstep:
  assumes "\<Turnstile> { conj P (holds_forall_hyper I bs) } [[i \<mapsto> (Cs1 i) | i \<in> I]] { Q }"
    and   "\<Turnstile> { conj P (holds_forall_hyper I (lnot_hyper bs)) } [[i \<mapsto> (Cs2 i) | i \<in> I]] { Q }"
    shows "\<Turnstile> { conj P (low_exp_hyper I bs)} [[ i \<mapsto> (if_then_else (bs i) (Cs1 i) (Cs2 i)) | i \<in> I ]] { Q }"
proof -
  from if_lockstep_true assms(1) have "\<Turnstile> { conj P (holds_forall_hyper I bs)} [[ i \<mapsto> (if_then_else (bs i) (Cs1 i) (Cs2 i)) | i \<in> I ]] { Q }" by force
  moreover from if_lockstep_false assms(2) have "\<Turnstile> { conj P (holds_forall_hyper I (lnot_hyper bs))} [[ i \<mapsto> (if_then_else (bs i) (Cs1 i) (Cs2 i)) | i \<in> I ]] { Q }" by force
  ultimately show ?thesis 
    unfolding relational_hyper_hoare_triple_def
  proof (intro ballI allI impI)
    fix S
    assume asm1:"\<forall>S. Logic.conj P (holds_forall_hyper I bs) S \<longrightarrow>
              Q (sem_lifted (map_comprehension (\<lambda>i. if_then_else (bs i) (Cs1 i) (Cs2 i)) (\<lambda>i. i \<in> I)) S)" and
          asm2:"\<forall>S. Logic.conj P (holds_forall_hyper I (lnot_hyper bs)) S \<longrightarrow>
              Q (sem_lifted (map_comprehension (\<lambda>i. if_then_else (bs i) (Cs1 i) (Cs2 i)) (\<lambda>i. i \<in> I)) S)" and
          asm3:"Logic.conj P (low_exp_hyper I bs) S"
    hence "conj P (holds_forall_hyper I bs) S \<or> conj P (holds_forall_hyper I (lnot_hyper bs)) S" using low_exp_either conj_def by metis
    thus "Q (sem_lifted (map_comprehension (\<lambda>i. if_then_else (bs i) (Cs1 i) (Cs2 i)) (\<lambda>i. i \<in> I)) S)"
    proof
      assume "Logic.conj P (holds_forall_hyper I bs) S"
      with asm1 show ?thesis by auto
    next 
      assume "Logic.conj P (holds_forall_hyper I (lnot_hyper bs)) S"
      with asm2 show ?thesis by auto
    qed
  qed
qed



abbreviation pick_branch where
"pick_branch P bs Cs1 Cs2 i  \<equiv> (if (entails P (\<lambda>S. (holds_forall (bs i) (S i)))) then (Cs1 i) else (Cs2 i))"


lemma if_equiv:
    shows "(let bs'  = (\<lambda>i. if entails P (\<lambda>S. holds_forall (bs i) (S i))
                  then bs i else lnot_hyper bs i);
         Cs1' = (\<lambda>i. if entails P (\<lambda>S. holds_forall (bs i) (S i))
                  then Cs1 i else Cs2 i);
         Cs2' = (\<lambda>i. if entails P (\<lambda>S. holds_forall (bs i) (S i))
                  then Cs2 i else Cs1 i)
     in  sem_equiv_hyper [ i \<mapsto> if_then_else (bs' i) (Cs1' i) (Cs2' i) | i \<in> I ]
                         [ i \<mapsto> if_then_else (bs i) (Cs1 i) (Cs2 i) | i \<in> I ] P)"
  apply(auto simp add:entails_def holds_forall_def lnot_def sem_equiv_hyper_def snd_def if_then_else_def sem_lifted_rewrite)
  apply(rule ext)
  apply(auto simp add:sem_def)
  apply (metis SemAssume SemIf2 SemSeq lnot_def lnot_hyper_def)
  apply (metis SemAssume SemIf1 SemSeq lnot_def lnot_hyper_def)
  apply (metis SemAssume SemIf2 SemSeq lnot_def lnot_hyper_def)
  by (metis SemAssume SemIf1 SemSeq lnot_def lnot_hyper_def)



definition hyper_emp where
  "hyper_emp I S \<longleftrightarrow> (\<forall>i \<in> I. (S i) = {})"


(* Executions of different programs can take different branches. *)
text\<open>
Generalization of the lockstep rules before. 
Executions of different programs can take different branches with this rule. 
\<close>
theorem if_lockstep_arbitrary:
    assumes "\<forall>i\<in>I. entails P (\<lambda>S. ((holds_forall (bs i) (S i)))) \<or> entails P (\<lambda>S. ((holds_forall (lnot (bs i)) (S i))))"
    and     "\<Turnstile> { P } [[ i \<mapsto> (pick_branch P bs Cs1 Cs2 i) | i \<in> I]] { Q }"
  shows     "\<Turnstile> { P } [[ i \<mapsto> (if_then_else (bs i) (Cs1 i) (Cs2 i)) | i \<in> I ]] { Q }"
proof -
  let ?bs' = "\<lambda>i. (if (entails P (\<lambda>S. (holds_forall (bs i) (S i)))) then (bs i) else (lnot_hyper bs i))"
  let ?Cs1' = "\<lambda>i. (if (entails P (\<lambda>S. (holds_forall (bs i) (S i)))) then (Cs1 i) else (Cs2 i))"
  let ?Cs2' = "\<lambda>i. (if (entails P (\<lambda>S. (holds_forall (bs i) (S i)))) then (Cs2 i) else (Cs1 i))"
  from assms if_equiv have equiv:"sem_equiv_hyper [ i \<mapsto> if_then_else (?bs' i) (?Cs1' i) (?Cs2' i) | i \<in> I ]
                         [ i \<mapsto> if_then_else (bs i) (Cs1 i) (Cs2 i) | i \<in> I ] P" by auto
  from assms(1) have hfa:"entails P (holds_forall_hyper I ?bs')"
    by(auto simp add:entails_def holds_forall_def holds_forall_hyper_def lnot_def lnot_hyper_def)
  hence ent_conj:"entails P (conj P (holds_forall_hyper I ?bs'))"
    by (metis (lifting) entail_conj entails_def)
  have "\<Turnstile> {conj P (holds_forall_hyper I ?bs')} [[ i \<mapsto> if_then_else (?bs' i) (?Cs1' i) (?Cs2' i) | i \<in> I ]] {Q}" 
  proof(rule if_lockstep_true)
    show "\<Turnstile> {Logic.conj P
         (holds_forall_hyper I (pick_branch P bs bs (lnot_hyper bs)))} [map_comprehension (pick_branch P bs Cs1 Cs2) (\<lambda>i. i \<in> I)] {Q}"
      unfolding relational_hyper_hoare_triple_def
    proof(intro allI impI)
      fix S
      assume "Logic.conj P (holds_forall_hyper I (pick_branch P bs bs (lnot_hyper bs))) S"
      hence "P S"
        by (simp add: conj_def)
      with assms(2) show "Q (sem_lifted (map_comprehension (pick_branch P bs Cs1 Cs2) (\<lambda>i. i \<in> I)) S)"
        by (simp add: relational_hyper_hoare_triple_def) 
    qed
  qed
  with ent_conj precondition_conseq have "\<Turnstile> {P} [[ i \<mapsto> if_then_else (?bs' i) (?Cs1' i) (?Cs2' i) | i \<in> I ]] {Q}" by auto
  with equiv rewrite_rule show ?thesis by auto
qed

section \<open>Loop alignment rules\<close>

subsection \<open>Fixed alignment rules\<close>

lemma least_or_none: "(\<exists>(n::nat). (P n) \<and> (\<forall>m<n. \<not>(P m))) \<or> (\<forall>(n::nat). \<not>(P n))"
  using exists_least_iff by auto


lemma hyper_seq_sem:
  "sem_lifted [ i \<mapsto> (Cs2 i) | i \<in> I ] (sem_lifted [ i \<mapsto> (Cs1 i) | i \<in> I ] S) = sem_lifted [ i \<mapsto> Seq (Cs1 i) (Cs2 i) | i \<in> I ] S"
  unfolding sem_lifted_def map_comprehension_def
  apply (rule ext)
     apply simp_all
  using sem_seq by blast


fun sem_lifted_after_n where
"sem_lifted_after_n 0 C S = S" |
"sem_lifted_after_n (Suc n) C S = sem_lifted C (sem_lifted_after_n n C S)"

definition pointwise_Union  where
  "pointwise_Union Sn f i = (\<Union>n\<in>Sn. (f n i))"

definition pointwise_union where
"pointwise_union f1 f2 i = (f1 i) \<union> (f2 i)"

lemma sem_lifted_after_n_combined: "sem_lifted_after_n n (map_comprehension Cs (\<lambda>i. i \<in> I)) (\<lambda>i.(sem_lifted_after_n 1 (map_comprehension Cs (\<lambda>i. i \<in> I)) S) i) = 
        sem_lifted_after_n (Suc n) (map_comprehension Cs (\<lambda>i. i \<in> I)) (S)"
  apply(simp)
  apply(induction n)
   apply(simp_all)
  done

lemma pointwise_Union_Sucn: "pointwise_Union UNIV (\<lambda>n. sem_lifted_after_n (Suc n) (map_comprehension Cs (\<lambda>i. i \<in> I)) (S)) i \<subseteq> pointwise_Union UNIV (\<lambda>n. sem_lifted_after_n n (map_comprehension Cs (\<lambda>i. i \<in> I)) (S)) i"
  unfolding pointwise_Union_def
proof -
  show "(\<Union>n. sem_lifted_after_n (Suc n) (map_comprehension Cs (\<lambda>i. i \<in> I)) S i)
    \<subseteq> (\<Union>n. sem_lifted_after_n n (map_comprehension Cs (\<lambda>i. i \<in> I)) S i)"
  proof
    fix x
    assume "x \<in> (\<Union>n. sem_lifted_after_n (Suc n) (map_comprehension Cs (\<lambda>i. i \<in> I)) S i)"
    thus "x \<in> (\<Union>n. sem_lifted_after_n n (map_comprehension Cs (\<lambda>i. i \<in> I)) S i)" apply(simp)
    proof -
      assume "\<exists>xa. x \<in> sem_lifted (map_comprehension Cs (\<lambda>i. i \<in> I)) (sem_lifted_after_n xa (map_comprehension Cs (\<lambda>i. i \<in> I)) S) i"
      from this obtain n where "x \<in> sem_lifted (map_comprehension Cs (\<lambda>i. i \<in> I)) (sem_lifted_after_n n (map_comprehension Cs (\<lambda>i. i \<in> I)) S) i" by blast
      hence fact: "x \<in> sem_lifted_after_n (Suc n) (map_comprehension Cs (\<lambda>i. i \<in> I)) S i" using sem_lifted_after_n_combined by auto
      show "\<exists>xa. x \<in> sem_lifted_after_n xa (map_comprehension Cs (\<lambda>i. i \<in> I)) S i"
      proof
        from fact show "x \<in> sem_lifted_after_n (Suc n) (map_comprehension Cs (\<lambda>i. i \<in> I)) S i" by auto
      qed
    qed
  qed
qed

lemma while_iter_reversed: 
  assumes "\<langle>While C, \<phi>\<rangle> \<rightarrow> \<sigma>" and "\<langle>C, \<sigma>\<rangle> \<rightarrow> \<sigma>'" 
  shows "\<langle>While C, \<phi>\<rangle> \<rightarrow> \<sigma>'"
proof -
  from assms(1) assms(2) show "\<langle>While C, \<phi>\<rangle> \<rightarrow> \<sigma>'"
  proof (induction "While C" \<phi> \<sigma> arbitrary: rule:single_sem.induct)
    case (SemWhileIter \<sigma> \<sigma>' \<sigma>'')
    then show ?case 
      using single_sem.SemWhileIter by blast
  next
    case (SemWhileExit \<sigma>)
    then show "\<langle>While C, \<sigma>\<rangle> \<rightarrow> \<sigma>'" by (auto simp add:single_sem.SemWhileIter single_sem.SemWhileExit)
  qed
qed


lemma while_union: "(sem_lifted [ i \<mapsto> While (Cs i)| i \<in> I ] S) 
      = (pointwise_Union (UNIV :: nat set) (\<lambda>n. (sem_lifted_after_n n [i \<mapsto> Cs i | i \<in> I] S)))"
proof - 
  have fact: "(\<lambda>i. if (i \<in> I) then (sem (While (Cs i)) (S i)) else (S i)) = (pointwise_Union (UNIV :: nat set) (\<lambda>n. (sem_lifted_after_n n [i \<mapsto> Cs i | i \<in> I] S)))"
    proof
    fix i
    show "(if i \<in> I then sem (While (Cs i)) (S i) else S i) =
         pointwise_Union UNIV (\<lambda>n. sem_lifted_after_n n (map_comprehension Cs (\<lambda>i. i \<in> I)) S) i"
    proof
      show "(if i \<in> I then sem (While (Cs i)) (S i) else S i)
    \<subseteq> pointwise_Union UNIV (\<lambda>n. sem_lifted_after_n n (map_comprehension Cs (\<lambda>i. i \<in> I)) S) i" 
      proof
        fix x
        assume asm: "x \<in> (if i \<in> I then sem (While (Cs i)) (S i) else S i)"
        have "i \<in> I \<or> i \<notin> I" by auto
        thus "x \<in> pointwise_Union UNIV (\<lambda>n. sem_lifted_after_n n (map_comprehension Cs (\<lambda>i. i \<in> I)) S) i"
        proof
          assume "i \<in> I"
          with asm have "x \<in> {x. \<exists>\<sigma>' \<sigma> l. x = (l, \<sigma>') \<and> (l, \<sigma>) \<in> S i \<and> \<langle>While (Cs i), \<sigma>\<rangle> \<rightarrow> \<sigma>'}" by (auto simp add:sem_def)
          hence "\<exists>\<sigma>' \<sigma> l. x = (l, \<sigma>') \<and> (l, \<sigma>) \<in> S i \<and> \<langle>While (Cs i), \<sigma>\<rangle> \<rightarrow> \<sigma>'" by auto
          from this obtain \<sigma>' \<sigma> l where fact2: "\<langle>While (Cs i), \<sigma>\<rangle> \<rightarrow> \<sigma>'" and fact3: "x = (l, \<sigma>')" and fact4: "(l, \<sigma>) \<in> S i" by blast
          from fact2 fact3 fact4 show "x \<in> pointwise_Union UNIV (\<lambda>n. sem_lifted_after_n n (map_comprehension Cs (\<lambda>i. i \<in> I)) S) i"
          proof (induction "While (Cs i)" \<sigma> \<sigma>' arbitrary: l S rule:single_sem.induct)
            case (SemWhileIter \<sigma> \<sigma>' \<sigma>'')
            have "(l, \<sigma>') \<in> (sem_lifted_after_n 1 (map_comprehension Cs (\<lambda>i. i \<in> I)) S) i" using \<open>i \<in> I\<close> \<open> (l, \<sigma>) \<in> S i\<close> \<open>\<langle>Cs i, \<sigma>\<rangle> \<rightarrow> \<sigma>'\<close>
              by (auto simp add:sem_lifted_rewrite sem_def)

            with SemWhileIter have "x \<in> pointwise_Union UNIV (\<lambda>n. sem_lifted_after_n n (map_comprehension Cs (\<lambda>i. i \<in> I)) (\<lambda>i.(sem_lifted_after_n 1 (map_comprehension Cs (\<lambda>i. i \<in> I)) S) i)) i"  by blast
            moreover have "\<And>n. sem_lifted_after_n n (map_comprehension Cs (\<lambda>i. i \<in> I)) (\<lambda>i.(sem_lifted_after_n 1 (map_comprehension Cs (\<lambda>i. i \<in> I)) S) i) = 
                            sem_lifted_after_n (Suc n) (map_comprehension Cs (\<lambda>i. i \<in> I)) (S)"
            proof - 
              fix n
              show "sem_lifted_after_n n (map_comprehension Cs (\<lambda>i. i \<in> I)) (\<lambda>i.(sem_lifted_after_n 1 (map_comprehension Cs (\<lambda>i. i \<in> I)) S) i) = 
                            sem_lifted_after_n (Suc n) (map_comprehension Cs (\<lambda>i. i \<in> I)) (S)"
                apply(simp)
                apply(induction n)
                 apply(simp_all)
                done
            qed
            ultimately have "x \<in> pointwise_Union UNIV (\<lambda>n. sem_lifted_after_n (Suc n) (map_comprehension Cs (\<lambda>i. i \<in> I)) (S)) i" by auto 
            then show ?case using pointwise_Union_Sucn by force
          next
            case (SemWhileExit \<sigma>)
            have "x \<in> sem_lifted_after_n 0 (map_comprehension Cs (\<lambda>i. i \<in> I)) S i"
              by (simp add: SemWhileExit.prems(1,2))
            then show ?case unfolding pointwise_Union_def by blast
          qed
        next
          assume "i \<notin> I"
          with asm have "x \<in> S i" by auto
          hence "x\<in> sem_lifted_after_n 0 (map_comprehension Cs (\<lambda>i. i \<in> I)) S i"
            by simp
          thus "x \<in> pointwise_Union UNIV (\<lambda>n. sem_lifted_after_n n (map_comprehension Cs (\<lambda>i. i \<in> I)) S) i" unfolding pointwise_Union_def by blast
        qed
      qed
    next 
      show "pointwise_Union UNIV (\<lambda>n. sem_lifted_after_n n (map_comprehension Cs (\<lambda>i. i \<in> I)) S) i
            \<subseteq> (if i \<in> I then sem (While (Cs i)) (S i) else S i)" 
      proof
        fix x
        assume asm: "x \<in> pointwise_Union UNIV (\<lambda>n. sem_lifted_after_n n (map_comprehension Cs (\<lambda>i. i \<in> I)) S) i"
        have "i\<in>I \<or> i\<notin>I" by auto
        thus "x \<in> (if i \<in> I then sem (While (Cs i)) (S i) else S i)"
        proof
          assume "i \<in> I"
          have "x\<in>{x. \<exists>\<sigma>' \<sigma> l. x = (l, \<sigma>') \<and> (l, \<sigma>) \<in> S i \<and> \<langle>While (Cs i), \<sigma>\<rangle> \<rightarrow> \<sigma>'}" 
          proof
            from asm[unfolded map_comprehension_def pointwise_Union_def] 
              have "x \<in> (\<Union>n. sem_lifted_after_n n (\<lambda>i. if i \<in> I then Some (Cs i) else None) S i)" by auto
              thus "\<exists>\<sigma>' \<sigma> l. x = (l, \<sigma>') \<and> (l, \<sigma>) \<in> S i \<and> \<langle>While (Cs i), \<sigma>\<rangle> \<rightarrow> \<sigma>'" apply(simp)
              proof -
                assume "\<exists>xa. x \<in> sem_lifted_after_n xa (\<lambda>i. if i \<in> I then Some (Cs i) else None) S i"
                from this obtain n where "x \<in> sem_lifted_after_n n (\<lambda>i. if i \<in> I then Some (Cs i) else None) S i" by auto
                thus ?thesis
                proof (induction n arbitrary:x)
                  case 0
                  hence "x\<in>S i" by auto
                  hence "\<exists>l \<sigma>. x = (l,\<sigma>)" by simp
                  from this obtain l \<sigma> where "x = (l,\<sigma>)" by blast
                  from this \<open>x\<in>S i\<close> have  "x = (l, \<sigma>) \<and> (l, \<sigma>) \<in> S i \<and> \<langle>While (Cs i), \<sigma>\<rangle> \<rightarrow> \<sigma> " by (auto simp add:SemWhileExit)
                  then show ?case by auto
                next
                  case (Suc n)
                  hence "x \<in> sem_lifted (\<lambda>i. if i \<in> I then Some (Cs i) else None) (sem_lifted_after_n n (\<lambda>i. if i \<in> I then Some (Cs i) else None) S) i" by auto
                  from this \<open>i \<in> I\<close>
                  have "x \<in> {x. \<exists>\<sigma>' \<sigma> l. x = (l, \<sigma>') \<and> (l, \<sigma>) \<in> sem_lifted_after_n n (\<lambda>i. if i \<in> I then Some (Cs i) else None) S i \<and> \<langle>Cs i, \<sigma>\<rangle> \<rightarrow> \<sigma>'}"
                    using sem_lifted_def sem_def by (smt (verit, ccfv_threshold) map_comprehension_def mem_Collect_eq sem_lifted_rewrite) 
                  hence "\<exists>\<sigma>' \<sigma> l. x = (l, \<sigma>') \<and> (l, \<sigma>) \<in> sem_lifted_after_n n (\<lambda>i. if i \<in> I then Some (Cs i) else None) S i \<and> \<langle>Cs i, \<sigma>\<rangle> \<rightarrow> \<sigma>'" by auto
                  from this obtain \<sigma>' \<sigma> l where fact_x:"x = (l, \<sigma>')" and fact_n: "(l, \<sigma>) \<in> sem_lifted_after_n n (\<lambda>i. if i \<in> I then Some (Cs i) else None) S i " and fact_step:"\<langle>Cs i, \<sigma>\<rangle> \<rightarrow> \<sigma>'" by blast
                  from fact_n Suc have "\<exists>\<phi>' \<phi> l'. (l, \<sigma>) = (l', \<phi>') \<and> (l', \<phi>) \<in> S i \<and> \<langle>While (Cs i), \<phi>\<rangle> \<rightarrow> \<phi>'" by auto
                  from this obtain \<phi>' \<phi> l' where "(l, \<sigma>) = (l', \<phi>')" and fact_\<phi>:"(l, \<phi>) \<in> S i" and fact_while_step:"\<langle>While (Cs i), \<phi>\<rangle> \<rightarrow> \<sigma>" by blast
                  from fact_while_step fact_step fact_x fact_\<phi> while_iter_reversed have "x = (l, \<sigma>') \<and> (l, \<phi>) \<in> S i \<and> \<langle>While (Cs i), \<phi>\<rangle> \<rightarrow> \<sigma>'" by blast
                  then show ?case by force
                qed
              qed
            qed
            thus "x \<in> (if i \<in> I then sem (While (Cs i)) (S i) else S i)" using \<open>i \<in> I\<close> by (auto simp add:sem_def)
        next 
          assume "i\<notin>I"
          have "x \<in> S i" 
          proof -
            from asm[unfolded map_comprehension_def pointwise_Union_def] 
            have "x \<in> (\<Union>n. sem_lifted_after_n n (\<lambda>i. if i \<in> I then Some (Cs i) else None) S i)" by auto
            thus ?thesis apply(simp)
            proof -
              assume "\<exists>xa. x \<in> sem_lifted_after_n xa (\<lambda>i. if i \<in> I then Some (Cs i) else None) S i "
              from this obtain n where "x \<in> sem_lifted_after_n n (\<lambda>i. if i \<in> I then Some (Cs i) else None) S i" by blast
              thus "x \<in> S i"
              proof (induction n)
                case 0
                then show ?case using \<open>i\<notin>I\<close> by auto
              next
                case (Suc n)
                hence "x \<in> sem_lifted (\<lambda>i. if i \<in> I then Some (Cs i) else None) (sem_lifted_after_n n (\<lambda>i. if i \<in> I then Some (Cs i) else None) S) i" by auto
                from this Suc show ?case using \<open>i\<notin>I\<close> by (auto simp add:sem_lifted_def)
              qed
            qed
          qed
          thus "x \<in> (if i \<in> I then sem (While (Cs i)) (S i) else S i)" using \<open>i \<notin> I\<close> by (auto)
        qed
      qed
    qed
  qed  
  show ?thesis by (simp add:fact sem_lifted_rewrite)
qed


lemma low_exp_always_all: "(low_exp_hyper I bs) S \<and> \<not>(holds_forall_hyper I (lnot_hyper bs) S) \<Longrightarrow> (holds_forall_hyper I bs S)"
  by (smt (verit, ccfv_threshold) holds_forall_hyper_def lnot_hyper_def low_exp_hyper_def)



lemma hyper_empty_low_exp: "conj (hyper_emp I) (low_exp_hyper I bs) (\<lambda>i. if (i \<in> I) then {} else (S i))"
  unfolding conj_def hyper_emp_def low_exp_hyper_def by simp

lemma pointwise_Union_sep_by_n: "(pointwise_Union (UNIV::nat set) P) = pointwise_union (pointwise_Union {i::nat | i. i \<le> n} P) (pointwise_Union {i::nat | i. i > n} P)"
  apply(rule ext)
  apply(auto simp add:pointwise_Union_def pointwise_union_def)
  using linorder_le_less_linear by auto


lemma outsideI_preserved: "\<And>i. i\<notin>I \<Longrightarrow> ((sem_lifted_after_n m [i \<mapsto> Cs i | i \<in> I] S) i = S i)"
proof -
  fix i
  assume "i\<notin>I"
  show "sem_lifted_after_n m (map_comprehension Cs (\<lambda>i. i \<in> I)) S i = S i"
  proof (induction m arbitrary: S)
    case 0
    then show ?case by auto
  next
    case (Suc m)
    then show ?case 
      by (simp add: \<open>i \<notin> I\<close> sem_lifted_rewrite)
  qed
qed

text\<open>
  Moves all while loops in a fixed lockstep. 
  They need to be synchronous and thus perform the same number of repetitions.
\<close>(*
theorem while_lockstep:
    assumes "\<Turnstile> { conj Iv (holds_forall_hyper I bs) } [[i \<mapsto> (Cs i) | i \<in> I]] { conj Iv (low_exp_hyper I bs)}"
    shows   "\<Turnstile> { conj Iv (low_exp_hyper I bs)} [[ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ]] { conj (disj Iv (hyper_emp I)) (holds_forall_hyper I (lnot_hyper bs))}"
proof -
  from assms[unfolded relational_hyper_hoare_triple_def] have "\<forall>S. conj Iv (holds_forall_hyper I bs) S \<longrightarrow>
      conj Iv (low_exp_hyper I bs) (sem_lifted [i \<mapsto> (Cs i) | i \<in> I] S) " by auto
  
  moreover have "\<forall>S. conj Iv (holds_forall_hyper I bs) S \<longrightarrow>
      conj Iv (holds_forall_hyper I bs) (sem_lifted [i \<mapsto> Assume (bs i) | i \<in> I] S)" 
  proof
    fix S
    show "conj Iv (holds_forall_hyper I bs) S \<longrightarrow>
      conj Iv (holds_forall_hyper I bs) (sem_lifted [i \<mapsto> Assume (bs i) | i \<in> I] S)"
    proof
      assume asm0:"conj Iv (holds_forall_hyper I bs) S"
      have "(\<lambda>i. if (i \<in> I) then (sem (Assume (bs i)) (S i)) else (S i)) = S" 
      proof
        fix i 
        have "i \<in> I \<or> i \<notin> I" by auto
        thus "(if i \<in> I then sem (Assume (bs i)) (S i) else S i) = S i"
        proof 
          assume asm: "i\<in>I"
          have "{x. \<exists>\<sigma>' \<sigma> l. x = (l, \<sigma>') \<and> (l, \<sigma>) \<in> S i \<and> \<langle>Assume (bs i), \<sigma>\<rangle> \<rightarrow> \<sigma>'} = S i" 
          proof
            show "{x. \<exists>\<sigma>' \<sigma> l. x = (l, \<sigma>') \<and> (l, \<sigma>) \<in> S i \<and> \<langle>Assume (bs i), \<sigma>\<rangle> \<rightarrow> \<sigma>'} \<subseteq> S i"
            proof
              fix x
              assume "x \<in> {x. \<exists>\<sigma>' \<sigma> l. x = (l, \<sigma>') \<and> (l, \<sigma>) \<in> S i \<and> \<langle>Assume (bs i), \<sigma>\<rangle> \<rightarrow> \<sigma>'}"
              hence "\<exists>\<sigma>' \<sigma> l. x = (l, \<sigma>') \<and> (l, \<sigma>) \<in> S i \<and> \<langle>Assume (bs i), \<sigma>\<rangle> \<rightarrow> \<sigma>'" by auto
              from this obtain \<sigma>' \<sigma> l where x_fact:"x = (l, \<sigma>')" and S_fact:"(l, \<sigma>) \<in> S i" and fact_asm: "\<langle>Assume (bs i), \<sigma>\<rangle> \<rightarrow> \<sigma>'" by metis
              from fact_asm have "\<sigma> = \<sigma>'"
              proof cases
                case SemAssume
                then show ?thesis by auto
              qed
              from x_fact S_fact this show "x \<in> S i" by auto
            qed
          next
            show "S i \<subseteq> {x. \<exists>\<sigma>' \<sigma> l. x = (l, \<sigma>') \<and> (l, \<sigma>) \<in> S i \<and> \<langle>Assume (bs i), \<sigma>\<rangle> \<rightarrow> \<sigma>'}"
            proof
              fix x
              assume asm: "x \<in> S i"
              hence "\<exists>l \<sigma>. x = (l,\<sigma>)" by auto
              from this obtain l \<sigma> where x_fact:"x = (l,\<sigma>)" by blast
              with asm have S_fact: "(l, \<sigma>) \<in> S i" by auto
              from asm0[unfolded holds_forall_hyper_def conj_def] \<open>i\<in>I\<close> \<open>(l, \<sigma>) \<in> S i\<close> have "bs i \<sigma>" by force
              hence "\<langle>Assume (bs i), \<sigma>\<rangle> \<rightarrow> \<sigma>" by (auto simp add: SemAssume)
              with x_fact S_fact have "x = (l, \<sigma>) \<and> (l, \<sigma>) \<in> S i \<and> \<langle>Assume (bs i), \<sigma>\<rangle> \<rightarrow> \<sigma>" by auto
              thus "x \<in> {x. \<exists>\<sigma>' \<sigma> l. x = (l, \<sigma>') \<and> (l, \<sigma>) \<in> S i \<and> \<langle>Assume (bs i), \<sigma>\<rangle> \<rightarrow> \<sigma>'}" 
                by (metis (mono_tags, lifting) mem_Collect_eq)
            qed
          qed
          thus "(if i \<in> I then sem (Assume (bs i)) (S i) else S i) = S i" using asm by (simp add:sem_def)
        next 
          assume "i\<notin>I"
          thus "(if i \<in> I then sem (Assume (bs i)) (S i) else S i) = S i" by auto
        qed
      qed
      with asm0 have H:"conj Iv (holds_forall_hyper I bs) (\<lambda>i. if (i \<in> I) then (sem (Assume (bs i)) (S i)) else (S i))" by auto
      thus "conj Iv (holds_forall_hyper I bs) (sem_lifted [i \<mapsto> Assume (bs i) | i \<in> I] S)" by (simp add: H sem_lifted_rewrite)
    qed
  qed

  ultimately have "\<forall>S. conj Iv (holds_forall_hyper I bs) S \<longrightarrow>
        conj Iv (low_exp_hyper I bs) (sem_lifted [i \<mapsto> (Cs i) | i \<in> I] (sem_lifted [i \<mapsto> Assume (bs i) | i \<in> I] S))"  by blast

  hence step_holds: "\<forall>S. conj Iv (holds_forall_hyper I bs) S \<longrightarrow>
      conj Iv (low_exp_hyper I bs) (sem_lifted [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)" using hyper_seq_sem
  proof -
    show ?thesis
      by (metis (no_types) \<open>\<forall>S. Logic.conj Iv (holds_forall_hyper I bs) S \<longrightarrow> Logic.conj Iv (low_exp_hyper I bs) (sem_lifted (map_comprehension Cs (\<lambda>i. i \<in> I)) (sem_lifted (map_comprehension (\<lambda>i. Assume (bs i)) (\<lambda>i. i \<in> I)) S))\<close> hyper_seq_sem)
  qed


  have while_is_union: "\<forall>S. (sem_lifted [ i \<mapsto> While (Assume (bs i);; Cs i)| i \<in> I ] S) 
      = (pointwise_Union (UNIV :: nat set) (\<lambda>n. (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)))"
    using while_union by auto

  have exists_n_or_not: "\<forall>S. (\<exists>n. (holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S) 
        \<and> (\<forall>m<n. \<not>(holds_forall_hyper I (lnot_hyper bs))(sem_lifted_after_n m [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)))
        \<or> (\<forall>n. \<not>(holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))" using least_or_none by auto

  have low_exp_preserved: "\<forall>S. conj Iv (low_exp_hyper I bs) S \<longrightarrow> 
        (\<forall>n. conj (disj Iv (hyper_emp I)) (low_exp_hyper I bs) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))"
    proof
    fix S
    show "conj Iv (low_exp_hyper I bs) S \<longrightarrow> 
        (\<forall>n. conj (disj Iv (hyper_emp I)) (low_exp_hyper I bs) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))"
    proof
      assume asm: "conj Iv (low_exp_hyper I bs) S"
      hence asm_fact:"(low_exp_hyper I bs) S" by (auto simp add:conj_def)
      with low_exp_either have "holds_forall_hyper I bs S \<or> holds_forall_hyper I (lnot_hyper bs) S"  by metis
      show "\<forall>n.  conj (disj Iv (hyper_emp I)) (low_exp_hyper I bs) (sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)"
      proof
        fix n
        show "conj (disj Iv (hyper_emp I)) (low_exp_hyper I bs) (sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)"
        proof (induction n)
          case 0
          with asm show ?case by (auto simp add:conj_def disj_def)
        next
          case (Suc n)
          hence "Iv (sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S) \<or> (hyper_emp I) (sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)"
            by (simp add: conj_def disj_def)
          then show ?case 
          proof
            assume iv_holds:"Iv (sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)"
            from Suc low_exp_either have "holds_forall_hyper I bs (sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S) \<or> holds_forall_hyper I (lnot_hyper bs) (sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)"
              by (metis (lifting) conj_def)
            thus "Logic.conj (Logic.disj Iv (hyper_emp I)) (low_exp_hyper I bs)
     (sem_lifted_after_n (Suc n) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)"
            proof 
              assume "holds_forall_hyper I bs (sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)"
              with iv_holds conj_def step_holds have "conj Iv (low_exp_hyper I bs) (sem_lifted (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) (sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S))"
                by (metis (mono_tags, lifting))
              thus "conj (Logic.disj Iv (hyper_emp I)) (low_exp_hyper I bs)
                  (sem_lifted_after_n (Suc n) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)"
                by (simp add: conj_def disj_def)
            next
              let ?S' = "(sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)"
              assume asm: "holds_forall_hyper I (lnot_hyper bs) ?S'"
              have "(\<lambda>i. if (i \<in> I) then (sem (Assume (bs i) ;; Cs i) (?S' i)) else (?S' i)) = (\<lambda>i. if (i \<in> I) then {} else (?S' i))"
              proof
                fix i 
                have "i\<in>I \<or> i\<notin>I"
                  by auto
                thus  "(if i \<in> I
                          then sem (Assume (bs i) ;; Cs i) (?S' i)
                            else (?S' i)) =
                            (if i \<in> I then {} else (?S' i))"
                proof
                  assume "i\<in>I"
                  have "sem (Assume (bs i) ;; Cs i) (?S' i) = {}" 
                    unfolding sem_def 
                  proof
                    show "{x.
                         \<exists>\<sigma>' \<sigma> l.
                            x = (l, \<sigma>') \<and>
                            (l, \<sigma>) \<in> ?S' i \<and>
                            \<langle>Assume (bs i) ;; Cs i, \<sigma>\<rangle> \<rightarrow> \<sigma>'}
                        \<subseteq> {}" using asm unfolding holds_forall_hyper_def lnot_hyper_def snd_def
                      apply(auto) 
                      using \<open>i \<in> I\<close> by auto
                  next 
                    show "{} \<subseteq> {x.
           \<exists>\<sigma>' \<sigma> l.
              x = (l, \<sigma>') \<and>
              (l, \<sigma>) \<in> (?S' i) \<and>
              \<langle>Assume (bs i) ;; Cs i, \<sigma>\<rangle> \<rightarrow> \<sigma>'}" by auto
                  qed
                  thus "(if i \<in> I
                          then sem (Assume (bs i) ;; Cs i) (?S' i)
                            else (?S' i)) =
                            (if i \<in> I then {} else (?S' i))" using \<open>i \<in> I\<close> by auto
                next
                  assume "i\<notin>I"
                  thus "(if i \<in> I
                          then sem (Assume (bs i) ;; Cs i) (?S' i)
                            else (?S' i)) =
                            (if i \<in> I then {} else (?S' i))" by auto
                qed
              qed
              hence H: "conj (hyper_emp I) (low_exp_hyper I bs) (\<lambda>i. if (i \<in> I) then (sem (Assume (bs i) ;; Cs i) (?S' i)) else (?S' i))" using hyper_empty_low_exp by force
              hence "conj (hyper_emp I) (low_exp_hyper I bs) (sem_lifted (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) ?S')"
                by (simp add: H sem_lifted_rewrite)
              thus "Logic.conj (Logic.disj Iv (hyper_emp I)) (low_exp_hyper I bs)
                    (sem_lifted_after_n (Suc n) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)"
                by (simp add: conj_def disj_def)
            qed
          next
            let ?S' = "(sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)"
            assume asm:"hyper_emp I ?S'"
            have "(\<lambda>i. if (i \<in> I) then (sem (Assume (bs i) ;; Cs i) (?S' i)) else (?S' i)) = (\<lambda>i. if (i \<in> I) then {} else (?S' i))"
            proof
              fix i 
              have "i\<in>I \<or> i\<notin>I"
                by auto
              thus  "(if i \<in> I
                        then sem (Assume (bs i) ;; Cs i) (?S' i)
                          else (?S' i)) =
                          (if i \<in> I then {} else (?S' i))"
              proof
                assume "i\<in>I"
                have "sem (Assume (bs i) ;; Cs i) (?S' i) = {}" 
                  unfolding sem_def 
                proof
                  show "{x.
                       \<exists>\<sigma>' \<sigma> l.
                          x = (l, \<sigma>') \<and>
                          (l, \<sigma>) \<in> ?S' i \<and>
                          \<langle>Assume (bs i) ;; Cs i, \<sigma>\<rangle> \<rightarrow> \<sigma>'}
                      \<subseteq> {}" using asm unfolding hyper_emp_def  snd_def
                    apply(auto) 
                    using \<open>i \<in> I\<close> by auto
                next 
                  show "{} \<subseteq> {x.
         \<exists>\<sigma>' \<sigma> l.
            x = (l, \<sigma>') \<and>
            (l, \<sigma>) \<in> (?S' i) \<and>
            \<langle>Assume (bs i) ;; Cs i, \<sigma>\<rangle> \<rightarrow> \<sigma>'}" by auto
                qed
                thus "(if i \<in> I
                        then sem (Assume (bs i) ;; Cs i) (?S' i)
                          else (?S' i)) =
                          (if i \<in> I then {} else (?S' i))" using \<open>i \<in> I\<close> by auto
              next
                assume "i\<notin>I"
                thus "(if i \<in> I
                        then sem (Assume (bs i) ;; Cs i) (?S' i)
                          else (?S' i)) =
                          (if i \<in> I then {} else (?S' i))" by auto
              qed
            qed
            hence H: "conj (hyper_emp I) (low_exp_hyper I bs) (\<lambda>i. if (i \<in> I) then (sem (Assume (bs i) ;; Cs i) (?S' i)) else (?S' i))" using hyper_empty_low_exp by force
            hence "conj (hyper_emp I) (low_exp_hyper I bs) (sem_lifted (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) ?S')"
              by (simp add: H sem_lifted_rewrite)
            thus "Logic.conj (Logic.disj Iv (hyper_emp I)) (low_exp_hyper I bs)
                  (sem_lifted_after_n (Suc n) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)"
              by (simp add: conj_def disj_def)
          qed
        qed
      qed
    qed
  qed


  have if_not_holdsforall_lnotbs_holdsforallbs: "\<forall>S. conj Iv (low_exp_hyper I bs) S \<longrightarrow> 
        (\<forall>n. \<not>(holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)
        \<longrightarrow> (holds_forall_hyper I bs) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))" using low_exp_preserved low_exp_always_all
    by (metis (mono_tags, lifting) conj_def)


  have exists_leastn_or_not: 
      "\<forall>S. conj Iv (low_exp_hyper I bs) S \<longrightarrow> (\<exists>n. (holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S) 
        \<and> (\<forall>m<n. (holds_forall_hyper I bs)(sem_lifted_after_n m [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)))
        \<or> (\<forall>n.   (holds_forall_hyper I bs) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))"
    using exists_n_or_not if_not_holdsforall_lnotbs_holdsforallbs by fastforce

  have fact1: "\<forall>S. conj Iv (low_exp_hyper I bs) S \<longrightarrow> 
        (\<forall>n. (holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S) \<longrightarrow> 
        (\<forall>m>n. (holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n m [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)
                \<and> (sem_lifted_after_n m [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)  = (\<lambda>i. if (i\<in>I) then {} else (sem_lifted_after_n m [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S) i )))"
  proof 
    fix S 
    show "conj Iv (low_exp_hyper I bs) S \<longrightarrow> 
        (\<forall>n. (holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S) \<longrightarrow> 
        (\<forall>m>n. (holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n m [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)
                \<and> (sem_lifted_after_n m [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)  = (\<lambda>i. if (i\<in>I) then {} else (sem_lifted_after_n m [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S) i )))"
    proof
      assume "conj Iv (low_exp_hyper I bs) S "
      show "(\<forall>n. (holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S) \<longrightarrow> 
        (\<forall>m>n. (holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n m [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)
                \<and> (sem_lifted_after_n m [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)  = (\<lambda>i. if (i\<in>I) then {} else (sem_lifted_after_n m [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S) i )))"
      proof
        fix n 
        show "(holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S) \<longrightarrow> 
        (\<forall>m>n. (holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n m [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)
                \<and> (sem_lifted_after_n m [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)  = (\<lambda>i. if (i\<in>I) then {} else (sem_lifted_after_n m [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S) i ))"
        proof
          assume asm_n:"holds_forall_hyper I (lnot_hyper bs) (sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)"
          show "(\<forall>m>n. (holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n m [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)
                \<and> (sem_lifted_after_n m [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)  = (\<lambda>i. if (i\<in>I) then {} else (sem_lifted_after_n m [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S) i ))"
          proof
            fix m
            show "n < m \<longrightarrow>
         (holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n m [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)
                \<and> (sem_lifted_after_n m [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)  = (\<lambda>i. if (i\<in>I) then {} else (sem_lifted_after_n m [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S) i )"
            proof
              assume asm: "n < m"
              hence "\<exists>m'. m = Suc m'" 
                using old.nat.exhaust by auto
              from this obtain m' where sucm':"m = Suc m'" by auto
              with asm have "n \<le> m'" by auto
              hence "(holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n (Suc m') [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)
                \<and> (sem_lifted_after_n (Suc m') [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)  = (\<lambda>i. if (i\<in>I) then {} else (sem_lifted_after_n (Suc m') [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S) i )"
              proof (induction m')
                case 0
                hence "n = 0" by auto
                with asm_n have asm_0: "holds_forall_hyper I (lnot_hyper bs) (sem_lifted_after_n 0 (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)" by auto
                show "holds_forall_hyper I (lnot_hyper bs) (sem_lifted_after_n (Suc 0) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S) \<and>
                      sem_lifted_after_n (Suc 0) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S =
                      (\<lambda>i. if i \<in> I then {} else sem_lifted_after_n (Suc 0) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i)"
                proof
                  from asm_0 show "holds_forall_hyper I (lnot_hyper bs) (sem_lifted_after_n (Suc 0) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)"
                    by (auto simp add:holds_forall_hyper_def lnot_hyper_def snd_def sem_lifted_rewrite sem_def)
                next
                  show "sem_lifted_after_n (Suc 0) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S =
                      (\<lambda>i. if i \<in> I then {} else sem_lifted_after_n (Suc 0) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i)"
                    apply(auto simp add:sem_lifted_rewrite)
                  proof
                    fix i
                    have "i\<in>I \<or> i\<notin>I" by auto
                    thus "(if i \<in> I then sem (Assume (bs i) ;; Cs i) (S i) else S i) =
                      (if i \<in> I then {} else sem_lifted_after_n (Suc 0) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i)"
                    proof
                      assume "i \<in> I"
                      with asm_0 show "(if i \<in> I then sem (Assume (bs i) ;; Cs i) (S i) else S i) =
                      (if i \<in> I then {} else sem_lifted_after_n (Suc 0) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i)"
                        by (auto simp add:holds_forall_hyper_def lnot_hyper_def snd_def sem_lifted_rewrite sem_def)
                    next 
                      assume "i\<notin>I"
                      with asm_0 show "(if i \<in> I then sem (Assume (bs i) ;; Cs i) (S i) else S i) =
                                              (if i \<in> I then {} else sem_lifted_after_n (Suc 0) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i)"
                        by (auto simp add:holds_forall_hyper_def lnot_hyper_def snd_def sem_lifted_rewrite sem_def)
                    qed
                  qed
                qed
              next
                case (Suc m'')
                hence "n = (Suc m'') \<or> n \<le> m''" by auto
                then show ?case 
                proof
                  assume asm: "n = Suc m''"
                  have eqa:"sem_lifted_after_n (Suc n) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S =
                  (\<lambda>i. if i \<in> I then {} else sem_lifted_after_n (Suc n) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i)"
                  proof -
                    show " sem_lifted_after_n (Suc n) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S =
    (\<lambda>i. if i \<in> I then {} else sem_lifted_after_n (Suc n) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i)"
                      apply(auto simp add:sem_lifted_rewrite)
                    proof
                      fix i
                      have "i\<in>I \<or> i \<notin> I" by auto
                      thus "(if i \<in> I then sem (Assume (bs i) ;; Cs i) (sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i)
          else sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i) =
         (if i \<in> I then {} else sem_lifted_after_n (Suc n) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i)"
                      proof
                        assume "i\<in>I"
                        with asm_n show "(if i \<in> I then sem (Assume (bs i) ;; Cs i) (sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i)
     else sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i) =
    (if i \<in> I then {} else sem_lifted_after_n (Suc n) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i)"
                          by (auto simp add:sem_def holds_forall_hyper_def lnot_hyper_def snd_def)
                      next
                        assume "i\<notin>I"
                        thus "(if i \<in> I then sem (Assume (bs i) ;; Cs i) (sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i)
     else sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i) =
    (if i \<in> I then {} else sem_lifted_after_n (Suc n) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i)"
                          by (auto simp add:sem_lifted_rewrite)
                      qed
                    qed
                  qed
                  moreover have "holds_forall_hyper I (lnot_hyper bs) (\<lambda>i. if i \<in> I then {} else sem_lifted_after_n (Suc n) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i)"
                    by (auto simp add:holds_forall_hyper_def)
                  ultimately have hfa: "holds_forall_hyper I (lnot_hyper bs) (sem_lifted_after_n (Suc n) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)" by auto
                  with asm hfa eqa show "holds_forall_hyper I (lnot_hyper bs) (sem_lifted_after_n (Suc (Suc m'')) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S) \<and>
    sem_lifted_after_n (Suc (Suc m'')) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S =
    (\<lambda>i. if i \<in> I then {} else sem_lifted_after_n (Suc (Suc m'')) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i)" by blast
                next
                  assume "n \<le> m''"
                  with Suc have hfa:"holds_forall_hyper I (lnot_hyper bs) (sem_lifted_after_n (Suc m'') (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)" and
                                eqa:"sem_lifted_after_n (Suc m'') (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S =
                                    (\<lambda>i. if i \<in> I then {} else sem_lifted_after_n (Suc m'') (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i)" by auto
                  from eqa have eqa:"sem_lifted_after_n (Suc (Suc m'')) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S =
    (\<lambda>i. if i \<in> I then {} else sem_lifted_after_n (Suc (Suc m'')) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i)"
                    apply(auto simp add:holds_forall_hyper_def lnot_hyper_def snd_def sem_def)
                  proof
                    fix i
                    have "i\<in>I \<or> i\<notin>I" by auto
                    thus " sem_lifted (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I))
          (\<lambda>i. if i \<in> I then {} else sem_lifted_after_n (Suc m'') (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i) i =
         (if i \<in> I then {} else sem_lifted_after_n (Suc (Suc m'')) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i)"
                    proof
                      assume "i \<in> I"
                      thus " sem_lifted (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I))
          (\<lambda>i. if i \<in> I then {} else sem_lifted_after_n (Suc m'') (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i) i =
         (if i \<in> I then {} else sem_lifted_after_n (Suc (Suc m'')) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i)"
                        by (auto simp add:sem_lifted_rewrite sem_def)
                      next 
                        assume "i\<notin>I"
                        thus "sem_lifted (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I))
          (\<lambda>i. if i \<in> I then {} else sem_lifted_after_n (Suc m'') (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i) i =
         (if i \<in> I then {} else sem_lifted_after_n (Suc (Suc m'')) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i)"
                          by (auto simp add:sem_lifted_rewrite sem_def)
                      qed
                    qed
                    moreover have "holds_forall_hyper I (lnot_hyper bs) (\<lambda>i. if i \<in> I then {} else sem_lifted_after_n (Suc (Suc m'')) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i)"
                      by (auto simp add:holds_forall_hyper_def)
                    ultimately have hfa: "holds_forall_hyper I (lnot_hyper bs) (sem_lifted_after_n (Suc (Suc m'')) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)" by auto
                    from eqa hfa show "holds_forall_hyper I (lnot_hyper bs) (sem_lifted_after_n (Suc (Suc m'')) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S) \<and>
    sem_lifted_after_n (Suc (Suc m'')) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S =
    (\<lambda>i. if i \<in> I then {} else sem_lifted_after_n (Suc (Suc m'')) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i)" by auto
                  qed
                qed
              with sucm' show "holds_forall_hyper I (lnot_hyper bs) (sem_lifted_after_n m (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S) \<and>
    sem_lifted_after_n m (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S =
    (\<lambda>i. if i \<in> I then {} else sem_lifted_after_n m (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i)" by auto
            qed
          qed
        qed
      qed
    qed
  qed

  have fact1p1:"\<forall>S. conj Iv (low_exp_hyper I bs) S \<longrightarrow> 
        (\<forall>n. (holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S) \<longrightarrow> 
        ((pointwise_Union {i::nat | i. i > n} (\<lambda>n. (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))) = (\<lambda>i. if (i\<in>I) then {} else (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S) i )))"
  proof
    fix S
    show "conj Iv (low_exp_hyper I bs) S \<longrightarrow> 
        (\<forall>n. (holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S) \<longrightarrow> 
        ((pointwise_Union {i::nat | i. i > n} (\<lambda>n. (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))) = (\<lambda>i. if (i\<in>I) then {} else (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S) i )))"
    proof
      assume asm1: "conj Iv (low_exp_hyper I bs) S"
      show "(\<forall>n. (holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S) \<longrightarrow> 
        ((pointwise_Union {i::nat | i. i > n} (\<lambda>n. (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))) = (\<lambda>i. if (i\<in>I) then {} else (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S) i )))"
      proof
        fix n
        show "holds_forall_hyper I (lnot_hyper bs) (sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S) \<longrightarrow>
         pointwise_Union {i |i. n < i} (\<lambda>n. sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S) =
         (\<lambda>i. if i \<in> I then {} else sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i)"
        proof
          assume asm2: "holds_forall_hyper I (lnot_hyper bs) (sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)"
          from asm1 asm2 fact1 have fact1_simp:"(\<forall>m>n. sem_lifted_after_n m (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S =
                       (\<lambda>i. if i \<in> I then {} else sem_lifted_after_n m (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i))" by auto
          show "pointwise_Union {i |i. n < i} (\<lambda>n. sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S) =
         (\<lambda>i. if i \<in> I then {} else sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i)" 
          proof
            fix i
            show "pointwise_Union {i |i. n < i} (\<lambda>n. sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S) i =
         (if i \<in> I then {} else sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i)"
              apply(auto simp add:pointwise_Union_def)
                apply (simp add: fact1_simp)
               apply(auto simp add:outsideI_preserved)
              done
          qed
        qed
      qed
    qed
  qed

  have fact2: "\<forall>S. conj Iv (low_exp_hyper I bs) S \<longrightarrow> 
        (\<forall>n. (holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S) 
        \<and> (\<forall>m<n. (holds_forall_hyper I bs) (sem_lifted_after_n m [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))
    \<longrightarrow> (pointwise_Union (UNIV :: nat set) (\<lambda>n. (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))) =  
        (pointwise_Union {i::nat | i. i \<le> n} (\<lambda>n. (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))))" 
  proof 
    fix S
    show "Logic.conj Iv (low_exp_hyper I bs) S \<longrightarrow>
         (\<forall>n. holds_forall_hyper I (lnot_hyper bs) (sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S) \<and>
              (\<forall>m<n. holds_forall_hyper I bs (sem_lifted_after_n m (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)) \<longrightarrow>
              pointwise_Union UNIV (\<lambda>n. sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S) =
              pointwise_Union {i |i. i \<le> n} (\<lambda>n. sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S))"
    proof
      assume asm: "Logic.conj Iv (low_exp_hyper I bs) S"
      show "\<forall>n. holds_forall_hyper I (lnot_hyper bs) (sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S) \<and>
        (\<forall>m<n. holds_forall_hyper I bs (sem_lifted_after_n m (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)) \<longrightarrow>
        pointwise_Union UNIV (\<lambda>n. sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S) =
        pointwise_Union {i |i. i \<le> n} (\<lambda>n. sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)"
      proof
        fix n
        show "holds_forall_hyper I (lnot_hyper bs) (sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S) \<and>
         (\<forall>m<n. holds_forall_hyper I bs (sem_lifted_after_n m (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)) \<longrightarrow>
         pointwise_Union UNIV (\<lambda>n. sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S) =
         pointwise_Union {i |i. i \<le> n} (\<lambda>n. sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)"
        proof
          assume "holds_forall_hyper I (lnot_hyper bs) (sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S) \<and>
                  (\<forall>m<n. holds_forall_hyper I bs (sem_lifted_after_n m (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S))"
          with fact1p1 have fact_hyper_empty:"((pointwise_Union {i::nat | i. i > n} (\<lambda>n. (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))) = (\<lambda>i. if (i\<in>I) then {} else (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S) i ))" 
            by (simp add: asm)
          have fact_union: "pointwise_union (pointwise_Union {i |i. i \<le> n} (\<lambda>n. sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)) (\<lambda>i. if (i\<in>I) then {} else (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S) i ) =
                pointwise_Union {i |i. i \<le> n} (\<lambda>n. sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)"
            apply(rule ext) 
            apply(auto simp add: pointwise_union_def pointwise_Union_def)
            done
          from pointwise_Union_sep_by_n have "pointwise_Union UNIV (\<lambda>n. sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S) =
    pointwise_union (pointwise_Union {i |i. i \<le> n} (\<lambda>n. sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)) (pointwise_Union {i::nat | i. i > n} (\<lambda>n. (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)))" by auto
          with fact_hyper_empty have "pointwise_Union UNIV (\<lambda>n. sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S) =
pointwise_union (pointwise_Union {i |i. i \<le> n} (\<lambda>n. sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)) (\<lambda>i. if (i\<in>I) then {} else (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S) i )" by force
          with fact_union show "pointwise_Union UNIV (\<lambda>n. sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S) =
    pointwise_Union {i |i. i \<le> n} (\<lambda>n. sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)" using fact1p1 fact_union by auto
        qed
      qed
    qed
  qed
            

  have fact3: "\<forall>S. conj Iv (low_exp_hyper I bs) S \<longrightarrow> 
        (\<forall>n. (holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S) 
        \<and> (\<forall>m<n. (holds_forall_hyper I bs) (sem_lifted_after_n m [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))
    \<longrightarrow> sem_lifted [ i \<mapsto> Assume (lnot (bs i)) | i \<in> I ] (pointwise_Union {i::nat | i. i \<le> n} (\<lambda>n. (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)))
        = (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))" 
  proof
    fix S
    show "conj Iv (low_exp_hyper I bs) S \<longrightarrow> 
        (\<forall>n. (holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S) 
        \<and> (\<forall>m<n. (holds_forall_hyper I bs) (sem_lifted_after_n m [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))
    \<longrightarrow> sem_lifted [ i \<mapsto> Assume (lnot (bs i)) | i \<in> I ] (pointwise_Union {i::nat | i. i \<le> n} (\<lambda>n. (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)))
        = (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))"
    proof
      assume "conj Iv (low_exp_hyper I bs) S"
      show " (\<forall>n. (holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S) 
        \<and> (\<forall>m<n. (holds_forall_hyper I bs) (sem_lifted_after_n m [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))
    \<longrightarrow> sem_lifted [ i \<mapsto> Assume (lnot (bs i)) | i \<in> I ] (pointwise_Union {i::nat | i. i \<le> n} (\<lambda>n. (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)))
        = (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))"
      proof
        fix n
        show "holds_forall_hyper I (lnot_hyper bs) (sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S) \<and>
         (\<forall>m<n. holds_forall_hyper I bs (sem_lifted_after_n m (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)) \<longrightarrow>
         sem_lifted (map_comprehension (\<lambda>i. Assume (lnot (bs i))) (\<lambda>i. i \<in> I))
          (pointwise_Union {i |i. i \<le> n} (\<lambda>n. sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)) =
         sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S"
        proof
          assume asm: "holds_forall_hyper I (lnot_hyper bs) (sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S) \<and>
    (\<forall>m<n. holds_forall_hyper I bs (sem_lifted_after_n m (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S))"
          show "sem_lifted (map_comprehension (\<lambda>i. Assume (lnot (bs i))) (\<lambda>i. i \<in> I))
                (pointwise_Union {i |i. i \<le> n} (\<lambda>n. sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)) =
                sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S"
          proof
            fix i
            from asm show "sem_lifted (map_comprehension (\<lambda>i. Assume (lnot (bs i))) (\<lambda>i. i \<in> I))
          (pointwise_Union {i |i. i \<le> n} (\<lambda>n. sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)) i =
         sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i"
              apply(auto simp add:sem_lifted_rewrite sem_def pointwise_Union_def lnot_def holds_forall_hyper_def lnot_hyper_def snd_def)
                apply (metis (mono_tags, lifting) case_prod_conv linorder_le_less_linear order_antisym_conv)
               apply (metis (mono_tags, lifting) SemAssume case_prod_conv lnot_def nle_le)
              by (simp add: outsideI_preserved)
          qed
        qed
      qed
    qed
  qed

  have fact4: "\<forall>S. conj Iv (low_exp_hyper I bs) S \<longrightarrow> 
        (\<forall>n. (holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S) 
        \<and> (\<forall>m<n. (holds_forall_hyper I bs) (sem_lifted_after_n m [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))
    \<longrightarrow> conj Iv  (holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))" 
  proof 
    fix S
    show "conj Iv (low_exp_hyper I bs) S \<longrightarrow> (\<forall>n. (holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S) 
        \<and> (\<forall>m<n. (holds_forall_hyper I bs) (sem_lifted_after_n m [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))
    \<longrightarrow> conj Iv  (holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))"
    proof
      assume asm: "conj Iv (low_exp_hyper I bs) S"
      show "(\<forall>n. (holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S) 
        \<and> (\<forall>m<n. (holds_forall_hyper I bs) (sem_lifted_after_n m [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))
    \<longrightarrow> conj Iv  (holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))"
      proof
        fix n 
        show "(holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S) 
        \<and> (\<forall>m<n. (holds_forall_hyper I bs) (sem_lifted_after_n m [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))
    \<longrightarrow> conj Iv  (holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)"
        proof
          assume asm2: "(holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S) 
        \<and> (\<forall>m<n. (holds_forall_hyper I bs) (sem_lifted_after_n m [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))"
          have factm: "(\<forall>m<n. conj Iv (holds_forall_hyper I bs) (sem_lifted_after_n m [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))" 
          proof
            fix m 
            show "m < n \<longrightarrow> Logic.conj Iv (holds_forall_hyper I bs) (sem_lifted_after_n m (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)"
            proof
              assume "m<n"
              thus "Logic.conj Iv (holds_forall_hyper I bs) (sem_lifted_after_n m (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)"
              proof (induction m)
                case 0
                with asm asm2 show ?case by(auto simp add:conj_def)
              next
                case (Suc m)
                hence "Logic.conj Iv (holds_forall_hyper I bs) (sem_lifted_after_n m (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)" by auto
                with step_holds have "Logic.conj Iv (low_exp_hyper I bs) (sem_lifted (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) (sem_lifted_after_n m (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S))" by auto
                with asm2 \<open>Suc m < n\<close> show ?case by(auto simp add:conj_def)
              qed
            qed
          qed
          
          from asm2 show "conj Iv  (holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)"
          proof (cases n)
            case 0
            with asm asm2 show ?thesis by (auto simp add:conj_def)
          next
            case (Suc n')
            hence "n' < n" by auto
            with factm have "Logic.conj Iv (holds_forall_hyper I bs) (sem_lifted_after_n n' (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)" by auto
            with step_holds have "Logic.conj Iv (low_exp_hyper I bs) (sem_lifted (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I))  (sem_lifted_after_n n' (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S))" by auto
            with asm2 \<open>n = Suc n'\<close> show ?thesis by(auto simp add:conj_def)
          qed
        qed
      qed
    qed
  qed


  have if_n_then_IV_and_holds_notbs: "\<forall>S. conj Iv (low_exp_hyper I bs) S \<longrightarrow>
        (\<exists>n. (holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S) 
        \<and> (\<forall>m<n. (holds_forall_hyper I bs) (sem_lifted_after_n m [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))) \<longrightarrow>
        conj Iv (holds_forall_hyper I (lnot_hyper bs))
       (sem_lifted [ i \<mapsto> Assume (lnot (bs i)) | i \<in> I ] (sem_lifted [ i \<mapsto> While (Assume (bs i);; Cs i)| i \<in> I ] S))" 
    by (metis (mono_tags, lifting) while_is_union fact2 fact3 fact4)


  have fact8: "\<forall>S. conj Iv (low_exp_hyper I bs) S \<longrightarrow> 
        ((\<forall>n. (holds_forall_hyper I bs) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)) \<longrightarrow> 
        (holds_forall_hyper I bs) (pointwise_Union (UNIV :: nat set) (\<lambda>n. (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))))"
  proof
    fix S
    show " conj Iv (low_exp_hyper I bs) S \<longrightarrow> 
        ((\<forall>n. (holds_forall_hyper I bs) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)) \<longrightarrow> 
        (holds_forall_hyper I bs) (pointwise_Union (UNIV :: nat set) (\<lambda>n. (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))))"
    proof
      assume "conj Iv (low_exp_hyper I bs) S"
      show "((\<forall>n. (holds_forall_hyper I bs) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)) \<longrightarrow> 
        (holds_forall_hyper I bs) (pointwise_Union (UNIV :: nat set) (\<lambda>n. (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))))"
      proof
        assume "\<forall>n. holds_forall_hyper I bs (sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)"
        thus "holds_forall_hyper I bs (pointwise_Union UNIV (\<lambda>n. sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S))"
          by(auto simp add:holds_forall_hyper_def pointwise_Union_def)
      qed
    qed
  qed

  have fact_prep9: "\<forall>S. conj Iv (low_exp_hyper I bs) S \<longrightarrow>
        (\<forall>n. (holds_forall_hyper I bs) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)) \<longrightarrow> 
         (sem_lifted [ i \<mapsto> Assume (lnot (bs i)) | i \<in> I ]  (pointwise_Union (UNIV :: nat set) (\<lambda>n. (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))))
          = (\<lambda>i. (if i\<in>I then {} else S i))" 
  proof
    fix S
    show "Logic.conj Iv (low_exp_hyper I bs) S \<longrightarrow>
         (\<forall>n. holds_forall_hyper I bs (sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)) \<longrightarrow>
         sem_lifted (map_comprehension (\<lambda>i. Assume (lnot (bs i))) (\<lambda>i. i \<in> I))
          (pointwise_Union UNIV (\<lambda>n. sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)) =
         (\<lambda>i. if i \<in> I then {} else S i)" (is "?P \<longrightarrow> (?R \<longrightarrow>?Q)")
    proof
      assume asm1: "?P"
      show "(?R \<longrightarrow>?Q)"
      proof
        assume asm2: "?R"
        show "?Q"
        proof
          fix i
          from asm2 show " sem_lifted (map_comprehension (\<lambda>i. Assume (lnot (bs i))) (\<lambda>i. i \<in> I))
          (pointwise_Union UNIV (\<lambda>n. sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)) i =
         (if i \<in> I then {} else S i)"
            apply(auto simp add:sem_lifted_rewrite sem_def pointwise_Union_def lnot_def holds_forall_hyper_def snd_def)
              apply(fastforce)
            by(auto simp add:outsideI_preserved)
        qed
      qed
    qed
  qed

  have fact9: "\<forall>S. conj Iv (low_exp_hyper I bs) S \<longrightarrow>
        (\<forall>n. (holds_forall_hyper I bs) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)) \<longrightarrow> 
        conj (hyper_emp I) (holds_forall_hyper I (lnot_hyper bs))
         (sem_lifted [ i \<mapsto> Assume (lnot (bs i)) | i \<in> I ]  (pointwise_Union (UNIV :: nat set) (\<lambda>n. (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))))"  
  proof
    fix S
    show "conj Iv (low_exp_hyper I bs) S \<longrightarrow> (\<forall>n. (holds_forall_hyper I bs) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)) \<longrightarrow> 
        conj (hyper_emp I) (holds_forall_hyper I (lnot_hyper bs))
         (sem_lifted [ i \<mapsto> Assume (lnot (bs i)) | i \<in> I ]  (pointwise_Union (UNIV :: nat set) (\<lambda>n. (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))))" (is "?P \<longrightarrow> (?R \<longrightarrow>?Q)")
    proof
      assume asm1: "?P"
      show "(?R \<longrightarrow>?Q)"
      proof
        assume asm2: "?R"
        have "conj (hyper_emp I) (holds_forall_hyper I (lnot_hyper bs)) (\<lambda>i. if i \<in> I then {} else S i) " 
          by(auto simp add:conj_def hyper_emp_def holds_forall_hyper_def)
        with fact_prep9 asm1 asm2 show "?Q" by force
      qed
    qed
  qed

  have if_exists_not_then_EMP_and_holds_notbs: "\<forall>S. conj Iv (low_exp_hyper I bs) S \<longrightarrow>
          (\<forall>n. (holds_forall_hyper I bs) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)) \<longrightarrow> 
          conj (hyper_emp I) (holds_forall_hyper I (lnot_hyper bs))
           (sem_lifted [ i \<mapsto> Assume (lnot (bs i)) | i \<in> I ] (sem_lifted [ i \<mapsto> While (Assume (bs i);; Cs i)| i \<in> I ] S))"  
    by (simp add: fact9 while_is_union)

  have "\<forall>S. conj Iv (low_exp_hyper I bs) S \<longrightarrow>
      conj (disj Iv (hyper_emp I)) (holds_forall_hyper I (lnot_hyper bs))
       (sem_lifted [ i \<mapsto> Assume (lnot (bs i)) | i \<in> I ] (sem_lifted [ i \<mapsto> While (Assume (bs i);; Cs i)| i \<in> I ] S))" 
    by (metis (mono_tags, lifting) conj_def disj_def exists_leastn_or_not if_n_then_IV_and_holds_notbs if_exists_not_then_EMP_and_holds_notbs)

  hence "\<forall>S. conj Iv (low_exp_hyper I bs) S \<longrightarrow>
      conj (disj Iv (hyper_emp I)) (holds_forall_hyper I (lnot_hyper bs))
       (sem_lifted [ i \<mapsto> While (Assume (bs i);; Cs i);; Assume (lnot (bs i)) | i \<in> I ] S)" by (auto simp add:hyper_seq_sem)

  thus ?thesis 
    by (simp add: relational_hyper_hoare_tripleI while_cond_def)
qed
*)


(*
fun repeat_with_bookmarks where
"repeat_with_bookmarks 0 b C = Skip" |
"repeat_with_bookmarks (Suc r) b C = Seq (if_then b C) (repeat_with_bookmarks r b C)"
*)
(*
text\<open>
  Moves the while loops with a variable fixed alignment. 
  They need to be synchronous with respect to the fixed alignment. 
  Version for a logic capable of trace sensitivity
\<close>
theorem while_fixed_alignment:
    assumes "\<Turnstile> { conj Iv (holds_forall_hyper I bs)} [[i \<mapsto> repeat_with_bookmarks (rf i) (Cs i) | i \<in> I]] { B(bs) F(conj Iv (low_exp_hyper I bs))}" 
    shows   "\<Turnstile> { conj Iv (low_exp_hyper I bs)} [[ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ]] { conj Iv (holds_forall_hyper I (lnot_hyper bs))}"
  
*)

fun repeat_with_if where
"repeat_with_if 0 b C = Skip" |
"repeat_with_if (Suc r) b C = Seq (if_then b C) (repeat_with_if r b C)"


inductive det_while_sem :: "('var, 'val) stmt \<Rightarrow> ('var, 'val) pstate \<Rightarrow> ('var, 'val) pstate \<Rightarrow> bool"
  ("\<langle>_, _\<rangle> \<rightarrow>det  _" [51,0] 81)
  where
  SemWhileIter: "\<lbrakk>b \<sigma>; \<langle>C, \<sigma>\<rangle> \<rightarrow> \<sigma>' ; \<langle>while_cond b C, \<sigma>'\<rangle> \<rightarrow>det \<sigma>'' \<rbrakk> \<Longrightarrow> \<langle>while_cond b C, \<sigma>\<rangle> \<rightarrow>det \<sigma>''"
| SemWhileExit: "\<not>b \<sigma> \<Longrightarrow> \<langle>while_cond b C, \<sigma>\<rangle> \<rightarrow>det \<sigma>"


lemma while_sem_equiv: "\<langle>while_cond b C, \<sigma>\<rangle> \<rightarrow> \<sigma>' = \<langle>while_cond b C, \<sigma>\<rangle> \<rightarrow>det \<sigma>'"
proof 
  assume "\<langle>while_cond b C, \<sigma>\<rangle> \<rightarrow> \<sigma>'"
  hence "\<langle>While (Assume b;; C);; Assume (lnot b), \<sigma>\<rangle> \<rightarrow> \<sigma>'" by (simp add:while_cond_def)
  from this obtain \<sigma>'' where "\<langle>While (Assume b;; C), \<sigma>\<rangle> \<rightarrow> \<sigma>''" and "\<langle>Assume (lnot b), \<sigma>''\<rangle> \<rightarrow> \<sigma>'"
    by (meson single_sem_Seq_elim)
  thus "\<langle>while_cond b C, \<sigma>\<rangle> \<rightarrow>det  \<sigma>'"
  proof (induction "While (Assume b;; C)" \<sigma> \<sigma>'')
    case (SemWhileIter \<sigma> \<sigma>''' \<sigma>'')
    hence "\<langle>while_cond b C, \<sigma>'''\<rangle> \<rightarrow>det  \<sigma>'" by auto
    moreover from \<open>\<langle>Assume b ;; C, \<sigma>\<rangle> \<rightarrow> \<sigma>'''\<close> have "b \<sigma>" and "\<langle>C, \<sigma>\<rangle> \<rightarrow> \<sigma>'''" by auto 
    ultimately show ?case
      by (simp add: det_while_sem.SemWhileIter)
  next
    case (SemWhileExit \<sigma>)
    hence "\<not>b \<sigma>"
      by (metis lnot_def single_sem_Assume_elim)
    then show ?case
      using det_while_sem.SemWhileExit local.SemWhileExit by auto
  qed
next
  assume "\<langle>while_cond b C, \<sigma>\<rangle> \<rightarrow>det  \<sigma>'"
  thus "\<langle>while_cond b C, \<sigma>\<rangle> \<rightarrow>  \<sigma>'"
  proof (induction)
    case (SemWhileIter b \<sigma> C \<sigma>' \<sigma>'')
    from this obtain \<sigma>''' where "\<langle>While (Assume b;; C), \<sigma>'\<rangle> \<rightarrow> \<sigma>'''" and "\<langle>Assume (lnot b), \<sigma>'''\<rangle> \<rightarrow> \<sigma>''"
      by (metis single_sem_Seq_elim while_cond_def)
    show ?case unfolding while_cond_def
      apply(rule single_sem.SemSeq)
       apply(rule single_sem.SemWhileIter)
        apply(rule single_sem.SemSeq)
         apply(rule single_sem.SemAssume)
         apply(simp add:\<open>b \<sigma>\<close>)
        apply(rule \<open>\<langle>C, \<sigma>\<rangle> \<rightarrow> \<sigma>'\<close>)
       apply(rule \<open>\<langle>While (Assume b;; C), \<sigma>'\<rangle> \<rightarrow> \<sigma>'''\<close>)
      apply(rule \<open>\<langle>Assume (lnot b), \<sigma>'''\<rangle> \<rightarrow> \<sigma>''\<close>)
      done
  next
    case (SemWhileExit b \<sigma> C)
    show ?case unfolding while_cond_def
      apply(rule single_sem.SemSeq)
       apply(rule single_sem.SemWhileExit)
      apply(rule single_sem.SemAssume)
      apply(simp add:lnot_def \<open>\<not>b \<sigma>\<close>)
      done
  qed
qed


lemma while_unfolded_sem_induction:
  assumes "\<langle>while_cond b C, \<sigma>\<rangle> \<rightarrow>det \<sigma>'" and "n > 0"
  shows "\<forall>m. \<exists>\<sigma>''. \<langle>(repeat_with_if m b C), \<sigma>\<rangle> \<rightarrow> \<sigma>'' \<and> \<langle>while_cond b (repeat_with_if n b C), \<sigma>''\<rangle> \<rightarrow>det \<sigma>'"
  using assms
proof(induction "while_cond b C" \<sigma> \<sigma>')
  case (SemWhileIter ba \<sigma> Ca \<sigma>' \<phi>)
  from this have bab: "ba = b \<and> Ca = C" unfolding while_cond_def
    by blast
  hence "ba = b" and "Ca = C" by auto
  from \<open>0 < n\<close> obtain n' where "n = Suc n'" using not0_implies_Suc by auto
  from SemWhileIter have repeats:"\<forall>m. \<exists>\<sigma>''. \<langle>repeat_with_if m b C, \<sigma>'\<rangle> \<rightarrow> \<sigma>'' \<and> \<langle>while_cond b (repeat_with_if n b C), \<sigma>''\<rangle> \<rightarrow>det  \<phi>" by blast
  from this obtain \<phi>' where n'_repeats: "\<langle>repeat_with_if n' b C, \<sigma>'\<rangle> \<rightarrow> \<phi>' \<and> \<langle>while_cond b (repeat_with_if n b C), \<phi>'\<rangle> \<rightarrow>det  \<phi>" by force
  show ?case 
    apply(intro ballI allI impI)
  proof -
    fix m
    show "\<exists>\<sigma>'''. \<langle>repeat_with_if m b C, \<sigma>\<rangle> \<rightarrow> \<sigma>''' \<and> \<langle>while_cond b (repeat_with_if n b C), \<sigma>'''\<rangle> \<rightarrow>det  \<phi>"
    proof (induction m)
      case 0
      then show ?case
      proof
        have "\<langle>repeat_with_if 0 b C, \<sigma>\<rangle> \<rightarrow> \<sigma>" 
          by (simp add: SemSkip)
        from \<open>ba \<sigma>\<close> \<open>\<langle>Ca, \<sigma>\<rangle> \<rightarrow> \<sigma>'\<close>  n'_repeats have "\<langle>repeat_with_if (Suc n') b C, \<sigma>\<rangle> \<rightarrow> \<phi>' "
          apply(auto simp add:if_then_def)
          apply(rule SemSeq)
           apply(rule SemIf1)
           apply(rule)
            apply(rule)
            apply(auto simp add:bab)
          done
        with \<open>n = Suc n'\<close> have "\<langle>repeat_with_if n b C, \<sigma>\<rangle> \<rightarrow> \<phi>' " by auto
        have "\<langle>while_cond b (repeat_with_if n b C), \<sigma>\<rangle> \<rightarrow>det  \<phi>"
          apply(rule det_while_sem.SemWhileIter)
          using SemWhileIter.hyps(1) \<open>ba = b\<close> apply auto[1]
          using \<open>\<langle>repeat_with_if n b C, \<sigma>\<rangle> \<rightarrow> \<phi>' \<close> apply auto[1]
          using n'_repeats apply auto
          done
        with \<open>\<langle>repeat_with_if 0 b C, \<sigma>\<rangle> \<rightarrow> \<sigma>\<close> show "\<langle>repeat_with_if 0 b C, \<sigma>\<rangle> \<rightarrow> \<sigma> \<and> \<langle>while_cond b (repeat_with_if n b C), \<sigma>\<rangle> \<rightarrow>det  \<phi>" by auto
      qed
    next
      case (Suc m')
      from this obtain \<sigma>''' where "\<langle>repeat_with_if m' b C, \<sigma>\<rangle> \<rightarrow> \<sigma>'''" and "\<langle>while_cond b (repeat_with_if n b C), \<sigma>'''\<rangle> \<rightarrow>det  \<phi>" by blast
      from repeats obtain \<phi>'' where "\<langle>repeat_with_if m' b C, \<sigma>'\<rangle> \<rightarrow> \<phi>''" and "\<langle>while_cond b (repeat_with_if n b C), \<phi>''\<rangle> \<rightarrow>det  \<phi>" by force
      from \<open>\<langle>repeat_with_if m' b C, \<sigma>'\<rangle> \<rightarrow> \<phi>''\<close> \<open>ba \<sigma>\<close> \<open>\<langle>Ca, \<sigma>\<rangle> \<rightarrow> \<sigma>'\<close> have "\<langle>repeat_with_if (Suc m') b C, \<sigma>\<rangle> \<rightarrow> \<phi>''"
          apply(auto simp add:if_then_def)
          apply(rule SemSeq)
           apply(rule SemIf1)
           apply(rule)
            apply(rule)
          apply(auto simp add:bab)
        done
      with \<open>\<langle>while_cond b (repeat_with_if n b C), \<phi>''\<rangle> \<rightarrow>det  \<phi>\<close> show ?case
        by blast
    qed
  qed
next
  case (SemWhileExit ba \<sigma> Ca)
  then show ?case 
    apply(intro ballI allI exI impI)
  proof -
    fix m
    assume "\<not> ba \<sigma>" and "while_cond ba Ca = while_cond b C"
    from this have "\<not> b \<sigma>" unfolding while_cond_def by auto
    show "\<langle>repeat_with_if m b C, \<sigma>\<rangle> \<rightarrow> \<sigma>  \<and> \<langle>while_cond b (repeat_with_if n b C), \<sigma>\<rangle> \<rightarrow>det  \<sigma>"
    proof (induction m)
      case 0
      then show ?case using \<open>\<not> b \<sigma>\<close>
        by (simp add: SemSkip det_while_sem.SemWhileExit)
    next
      case (Suc m)
      then show ?case using \<open>\<not> b \<sigma>\<close> 
        apply(auto simp add:if_then_def)
        by (metis SemAssume SemIf2 SemSeq lnot_def)
    qed
  qed
qed



lemma while_unfolded_sem: "n > 0 \<Longrightarrow> sem (while_cond b C) S  = sem (while_cond b (repeat_with_if n b C)) S"
  apply(auto simp add:sem_def)
proof-
  fix \<sigma>' \<sigma> l
  assume "0 < n"
  assume "(l, \<sigma>) \<in> S"
  assume "\<langle>while_cond b C, \<sigma>\<rangle> \<rightarrow> \<sigma>'"
  hence "\<langle>while_cond b C, \<sigma>\<rangle> \<rightarrow>det \<sigma>'"
    by (simp add: while_sem_equiv)
  with while_unfolded_sem_induction \<open>0 < n\<close>
  obtain \<sigma>'' where "\<langle>(repeat_with_if 0 b C), \<sigma>\<rangle> \<rightarrow> \<sigma>'' \<and> \<langle>while_cond b (repeat_with_if n b C), \<sigma>''\<rangle> \<rightarrow>det \<sigma>'" by blast
  moreover from this have "\<sigma>'' = \<sigma>" by auto
  ultimately show "\<exists>\<sigma>. (l, \<sigma>) \<in> S \<and> \<langle>while_cond b (repeat_with_if n b C), \<sigma>\<rangle> \<rightarrow> \<sigma>'" using \<open>(l, \<sigma>) \<in> S\<close> by (auto simp add: while_sem_equiv) 
next
  fix \<sigma>' \<sigma> l
  assume "0 < n"
  assume "(l, \<sigma>) \<in> S"
  assume "\<langle>while_cond b (repeat_with_if n b C), \<sigma>\<rangle> \<rightarrow> \<sigma>'"
  hence "\<langle>while_cond b (repeat_with_if n b C), \<sigma>\<rangle> \<rightarrow>det \<sigma>'" by (auto simp add: while_sem_equiv) 
  hence "\<langle>while_cond b C, \<sigma>\<rangle> \<rightarrow>det \<sigma>'"
  proof(induction "while_cond b (repeat_with_if n b C)" \<sigma> \<sigma>' rule:det_while_sem.induct)
    case (SemWhileIter ba \<sigma> Ca \<sigma>' \<sigma>'')
    from SemWhileIter have "b \<sigma>" unfolding while_cond_def by simp
    from SemWhileIter have "\<langle>(repeat_with_if n b C), \<sigma>\<rangle> \<rightarrow> \<sigma>'" unfolding while_cond_def by simp
    moreover from SemWhileIter have  "\<langle>while_cond b C, \<sigma>'\<rangle> \<rightarrow>det  \<sigma>''" by auto
    ultimately show ?case 
    proof (induction n arbitrary: \<sigma>)
      case 0
      then show ?case by auto
    next
      case (Suc n)
      hence "\<langle>if_then b C ;; repeat_with_if n b C, \<sigma>\<rangle> \<rightarrow> \<sigma>'" by auto
      from this obtain \<phi> where "\<langle>if_then b C, \<sigma>\<rangle> \<rightarrow> \<phi>" and "\<langle>repeat_with_if n b C, \<phi>\<rangle> \<rightarrow> \<sigma>'" by auto
      from \<open>\<langle>if_then b C, \<sigma>\<rangle> \<rightarrow> \<phi>\<close> have \<phi>_cond:"\<phi> = \<sigma> \<or> (b \<sigma> \<and> \<langle>C, \<sigma>\<rangle> \<rightarrow> \<phi>)" unfolding if_then_def by auto
      from \<open>\<langle>repeat_with_if n b C, \<phi>\<rangle> \<rightarrow> \<sigma>'\<close> Suc have while_\<phi>:"\<langle>while_cond b C, \<phi>\<rangle> \<rightarrow>det  \<sigma>''" by auto
      from \<phi>_cond show ?case
      proof
        assume "\<phi> = \<sigma>"
        thus ?thesis using while_\<phi> by blast
      next
        assume "b \<sigma> \<and> \<langle>C, \<sigma>\<rangle> \<rightarrow> \<phi>"
        hence "b \<sigma>" and "\<langle>C, \<sigma>\<rangle> \<rightarrow> \<phi>" by auto
        thus ?thesis using while_\<phi>
          by (simp add: det_while_sem.SemWhileIter)
      qed
    qed
  next
    case (SemWhileExit ba \<sigma> Ca)
    hence "\<not> b \<sigma>" unfolding while_cond_def by simp
    show ?case
      apply(rule det_while_sem.SemWhileExit)
      by (simp add: \<open>\<not> b \<sigma>\<close>)
  qed
  thus "\<exists>\<sigma>. (l, \<sigma>) \<in> S \<and> \<langle>while_cond b C, \<sigma>\<rangle> \<rightarrow> \<sigma>'" using \<open>(l, \<sigma>) \<in> S\<close> by (auto simp add:while_sem_equiv)
qed


lemma while_unfolded: "(\<forall>i\<in>I. (rf i) > 0) \<Longrightarrow> sem_lifted [ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ] S = (sem_lifted [ i \<mapsto> while_cond (bs i) (repeat_with_if (rf i) (bs i) (Cs i)) | i \<in> I ] S)"
  apply(simp only: sem_lifted_rewrite)
  apply(rule ext)
  apply(simp add: outsideI_preserved)
  apply(intro impI)
  using while_unfolded_sem by blast

(*
theorem while_fixed_alignment:
  assumes "\<Turnstile> { conj Iv (holds_forall_hyper I bs)} [[i \<mapsto> repeat_with_if (rf i) (bs i) (Cs i) | i \<in> I]] { conj Iv (low_exp_hyper I bs)}" 
      and "(\<forall>i\<in>I. (rf i) > 0)"
    shows "\<Turnstile> { conj Iv (low_exp_hyper I bs)} [[ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ]] { conj (disj Iv (hyper_emp I)) (holds_forall_hyper I (lnot_hyper bs))}"
proof -
  from assms(1) while_lockstep have "\<Turnstile> { conj Iv (low_exp_hyper I bs)} [[ i \<mapsto> (while_cond (bs i) (repeat_with_if (rf i) (bs i) (Cs i))) | i \<in> I ]] { conj (disj Iv (hyper_emp I)) (holds_forall_hyper I (lnot_hyper bs))}" by auto
  with assms(2) show ?thesis unfolding relational_hyper_hoare_triple_def using while_unfolded 
    by (metis (mono_tags, lifting))
qed*)

(*1. Needed to abolish the idea of proving the equality of the sem_after_m_steps and the while semantics directly, as the induction could not be performed because of induction step of the while only did advance by one step and i needed rf(i) steps*)
(*
proof (intro ballI allI impI, simp only:sem_lifted_rewrite)
  fix S
  assume asm: "conj Iv (low_exp_hyper I bs) S"
  from assms have "\<forall>S. conj Iv (holds_forall_hyper I bs) S \<longrightarrow>
      conj Iv (low_exp_hyper I bs) (\<lambda>i. if i \<in> I then sem (repeat_with_if (rf i) (bs i) (Cs i)) (S i) else S i)"
    by (simp add:relational_hyper_hoare_triple_def sem_lifted_rewrite)

  have exists_leastn_or_not: 
          "\<forall>S. conj Iv (low_exp_hyper I bs) S \<longrightarrow> 
            (\<exists>n. (holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n n [i \<mapsto> repeat_with_if (rf i) (bs i) (Cs i) | i \<in> I] S) 
            \<and> (\<forall>m<n. (holds_forall_hyper I bs) (sem_lifted_after_n m [i \<mapsto> repeat_with_if (rf i) (bs i) (Cs i) | i \<in> I] S)))
            \<or> (\<forall>n.   (holds_forall_hyper I bs) (sem_lifted_after_n n [i \<mapsto> repeat_with_if (rf i) (bs i) (Cs i) | i \<in> I] S))"
    sorry
  have  "(\<lambda>i. if i \<in> I then sem (While (Assume (bs i) ;; Cs i)) (S i) else S i) =
         (pointwise_Union (UNIV :: nat set) (\<lambda>n. (sem_lifted_after_n n [i \<mapsto> repeat_with_if (rf i) (bs i) (Cs i) | i \<in> I] S)))" 
    sorry
  from exists_leastn_or_not asm have "(\<exists>n. (holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n n [i \<mapsto> repeat_with_if (rf i) (bs i) (Cs i) | i \<in> I] S) 
            \<and> (\<forall>m<n. (holds_forall_hyper I bs) (sem_lifted_after_n m [i \<mapsto> repeat_with_if (rf i) (bs i) (Cs i) | i \<in> I] S)))
            \<or> (\<forall>n.   (holds_forall_hyper I bs) (sem_lifted_after_n n [i \<mapsto> repeat_with_if (rf i) (bs i) (Cs i) | i \<in> I] S))" (is "?A \<or> ?B") by auto
  thus "conj (disj Iv (hyper_emp I)) (holds_forall_hyper I (lnot_hyper bs))
          (\<lambda>i. if i \<in> I then sem (while_cond (bs i) (Cs i)) (S i) else S i)" (is "?P") 
  proof 
    assume "?A"
    from this obtain n where 
          "(holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n n [i \<mapsto> repeat_with_if (rf i) (bs i) (Cs i) | i \<in> I] S)" 
      and "(\<forall>m<n. (holds_forall_hyper I bs) (sem_lifted_after_n m [i \<mapsto> repeat_with_if (rf i) (bs i) (Cs i) | i \<in> I] S))" by auto
    have "(\<lambda>i. if i \<in> I then sem (while_cond (bs i) (Cs i)) (S i) else S i) = 
      (sem_lifted_after_n n [i \<mapsto> repeat_with_if (rf i) (bs i) (Cs i) | i \<in> I] S)"
      apply(rule ext)
      apply(auto simp add:sem_def outsideI_preserved)
    proof -
      fix i \<sigma>' \<sigma> l
      assume "\<langle>while_cond (bs i) (Cs i), \<sigma>\<rangle> \<rightarrow> \<sigma>'" and "(l, \<sigma>) \<in> S i" and "i \<in> I"
      hence  "\<langle>while_cond (bs i) (Cs i), \<sigma>\<rangle> \<rightarrow>det \<sigma>'" and "(l, \<sigma>) \<in> S i" and "i \<in> I" using while_sem_equiv by auto

      have "(l, \<sigma>') \<in> sem_lifted_after_n (m+n) (map_comprehension (\<lambda>i. repeat_with_if (rf i) (bs i) (Cs i)) (\<lambda>i. i \<in> I)) (sem_lifted_after_n m (map_comprehension (\<lambda>i. repeat_with_if (rf i) (bs i) (Cs i)) (\<lambda>i. i \<in> I)) S) i" 
        if asms:"\<langle>while_cond (bs i) (Cs i), \<sigma>\<rangle> \<rightarrow>det \<sigma>'" "i \<in> I" "(l, \<sigma>) \<in> sem_lifted_after_n m (map_comprehension (\<lambda>i. repeat_with_if (rf i) (bs i) (Cs i)) (\<lambda>i. i \<in> I)) S i" "m<n"
        for m
        using asms
      proof (induction arbitrary: m rule:det_while_sem.induct)
        case (SemWhileIter b \<sigma> C \<sigma>' \<sigma>'')
        then show ?case sorry
      next
        case (SemWhileExit b \<sigma> C)
        then show ?case sorry
      qed

      thus "(l, \<sigma>') \<in> sem_lifted_after_n n (map_comprehension (\<lambda>i. repeat_with_if (rf i) (bs i) (Cs i)) (\<lambda>i. i \<in> I)) S i"
      proof (induction arbitrary:S)
        case (SemWhileIter b \<sigma> C \<sigma>' \<sigma>'')
        then show ?case sorry
      next
        case (SemWhileExit b \<sigma> C)
        then show ?case sorry
      qed
    thus "?P" sorry
  next
    assume "?B"
    show "?P" sorry
qed
*)

fun repeat_program where 
"repeat_program (Suc 0) C = C" |
"repeat_program (Suc r) C = Seq C (repeat_program r C)"

definition sum_upto :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) option" where
  "sum_upto f v =
     while_option
       (\<lambda>(i, s). (s + f i \<le> v))                
       (\<lambda>(i, s). (Suc i, s + f i))      
       (0, 0)"       

definition sum_upto_sum :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat option" where
  "sum_upto_sum f v = map_option snd (sum_upto f v)"

definition sum_upto_n :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat option" where
  "sum_upto_n f v = map_option fst (sum_upto f v)"

fun traces_before_alignment_get_j where
"traces_before_alignment_get_j rf i = sum_upto_n rf i"

fun traces_before_alignment_get_k where
"traces_before_alignment_get_k rf i = (case (sum_upto_sum rf i) of None \<Rightarrow> None | Some s \<Rightarrow> Some (i-s))"
                       
fun traces_before_alignment where
"traces_before_alignment rf Cs i =
  (let j = traces_before_alignment_get_j rf i;
       k = traces_before_alignment_get_k rf i
   in case k of
        None   \<Rightarrow> None
      | Some k' \<Rightarrow>
          (case j of
             None    \<Rightarrow> None
           | Some j' \<Rightarrow> Some (repeat_program (rf j' - k') (Cs j'))))"

fun traces_before_alignment_conditions where
"traces_before_alignment_conditions rf bs i = undefined"

fun traces_before_alignment_set where
"traces_before_alignment_set rf I  = undefined"

fun traces_before_alignment_invariant where
"traces_before_alignment_invariant rf Iv i = undefined"




text\<open> 
  Moves the while loops with a variable fixed alignment. 
  They need to be synchronous with respect to the fixed alignment. 
  Version working in the current logic. 
  Feels unnatural.
\<close>
(*
theorem while_fixed_alignment2:
    assumes "\<Turnstile> { conj Iv (holds_forall_hyper I bs)} [[i \<mapsto> repeat_program (rf i) (Cs i) | i \<in> I]] { conj Iv (low_exp_hyper I bs)}" 
    and     "\<Turnstile> { conj  (traces_before_alignment_invariant rf Iv) (holds_forall_hyper (traces_before_alignment_set rf I) (traces_before_alignment_conditions rf bs))} 
                [traces_before_alignment rf Cs] 
               { holds_forall_hyper (traces_before_alignment_set rf I) (traces_before_alignment_conditions rf bs)}"
    shows   "\<Turnstile> { conj Iv (low_exp_hyper I bs)} [[ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ]] { conj Iv (holds_forall_hyper I (lnot_hyper bs))}"
  
*)

subsection \<open>Non-Fixed alignment rules\<close>

definition holds_for_prog where
"holds_for_prog j bs S \<longleftrightarrow> (\<forall>\<phi>\<in>(S j). (bs j) (snd \<phi>))"

definition disj_I where
"disj_I I Ps S \<longleftrightarrow> (\<exists>i\<in>I. (Ps i) S)"


text\<open>Projects out all empty sets. 
      As a postcondition, this hyper-assertion says:
        The postcondition P holds, if it does not consider the non-terminating programs.\<close>
definition if_terminates where
"if_terminates P S = (\<exists>S'. P (\<lambda>i. if (S i = {}) then (S' i) else (S i)))"

definition holds_for_prog_set where
"holds_for_prog_set J bs = holds_forall_hyper J bs"


abbreviation can_step_subset_or_all_finished where
"can_step_subset_or_all_finished I bs V \<equiv> (disj (disj_I (Pow I - {{}}) (\<lambda>J. conj (holds_for_prog_set J bs) (V J))) (holds_forall_hyper I (lnot_hyper bs)))"

abbreviation can_step_any_unfinished where
"can_step_any_unfinished I bs V S \<equiv> (\<forall>i\<in>I. \<not>(holds_forall (lnot (bs i)) (S i)) \<longrightarrow> (\<exists>J\<in>(Pow I). i\<in>J \<and> (conj (holds_for_prog_set J bs) (V J) S)))"




fun loop_cond_assert_rec :: "'a list \<Rightarrow> 'a nstate list \<Rightarrow> (nat \<Rightarrow> 'a npstate \<Rightarrow> bool) \<Rightarrow>'a syn_assertion \<Rightarrow> 'a hyper_set \<Rightarrow> bool" where
  "loop_cond_assert_rec vals states bs (AConst b) _ \<longleftrightarrow> b"
| "loop_cond_assert_rec vals states bs (AComp e1 cmp e2) _ \<longleftrightarrow> cmp (interp_exp vals states e1) (interp_exp vals states e2)"
| "loop_cond_assert_rec vals states bs (AForallState i A) S \<longleftrightarrow> (\<forall>\<phi> \<in> S i. loop_cond_assert_rec vals (\<phi> # states) bs A S)"
| "loop_cond_assert_rec vals states bs (AExistsState i A) S \<longleftrightarrow> (\<exists>\<phi>. loop_cond_assert_rec vals (\<phi> # states) bs A S \<and> (lnot (bs i) (snd \<phi>) \<longrightarrow> \<phi> \<in> (S i)))"
| "loop_cond_assert_rec vals states bs (AForall A) S \<longleftrightarrow> (\<forall>v. loop_cond_assert_rec (v # vals) states bs A S)"
| "loop_cond_assert_rec vals states bs (AExists A) S \<longleftrightarrow> (\<exists>v. loop_cond_assert_rec (v # vals) states bs A S)"
| "loop_cond_assert_rec vals states bs (AAnd A B) S \<longleftrightarrow> (loop_cond_assert_rec vals states bs A S \<and> loop_cond_assert_rec vals states bs B S)"
| "loop_cond_assert_rec vals states bs (AOr A B) S \<longleftrightarrow> (loop_cond_assert_rec vals states bs A S \<or> loop_cond_assert_rec vals states bs B S)"

abbreviation loop_cond_assert where
"loop_cond_assert bs P \<equiv> loop_cond_assert_rec [] [] bs P"


lemma can_step_any_unfinished_can_step_subset_or_all_finished:
  assumes "entails Iv (can_step_any_unfinished I bs V)"
  shows "entails Iv (can_step_subset_or_all_finished I bs V)"
  using assms
  apply(auto simp add:entails_def holds_forall_def conj_def holds_for_prog_set_def holds_forall_hyper_def disj_def lnot_hyper_def)
  unfolding disj_I_def conj_def holds_forall_hyper_def
  by (metis Pow_bottom empty_iff insertE insert_Diff lnot_def snd_conv)




(*theorem while_nonfixed_alignment:
  assumes   "\<forall>J\<in>(Pow I - {{}}). \<Turnstile> { conj (interp_assert Iv) (conj (holds_for_prog_set J bs) (V J))} [[i \<mapsto> prog_set_or_skip J Cs i | i \<in> I]] { (interp_assert Iv) }"
      and   "entails (interp_assert Iv) (can_step_any_unfinished I bs V)"
    shows   "\<Turnstile> { (interp_assert Iv) } [[ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ]] { conj (loop_cond_assert bs Iv) (holds_forall_hyper I (lnot_hyper bs))}"
  sorry*)


(*theorem while_lockstep_syn: (*We derive a version of while_lockstep with a syntactic invariant in order to be able to derive it using while_nonfixed_alignment*)
  assumes "\<Turnstile> { conj (interp_assert Iv) (holds_forall_hyper I bs) } [[i \<mapsto> (Cs i) | i \<in> I]] { (interp_assert Iv)}"
      and "entails (interp_assert Iv) (low_exp_hyper I bs)" (*The idea of while_lockstep rule stays roughly the same. It would be more ideal though if it had implied the original.*)
    shows "\<Turnstile> { (interp_assert Iv) } [[ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ]] { conj (disj (interp_assert Iv) (hyper_emp I)) (holds_forall_hyper I (lnot_hyper bs))}"
proof -
  let ?V = "\<lambda>J. if J = I then (\<lambda>S. True) else (\<lambda>S. False)"
  have H1: "\<forall>J\<in>(Pow I - {{}}). \<Turnstile> { conj (interp_assert Iv) (conj (holds_for_prog_set J bs) (?V J))} [[i \<mapsto> prog_set_or_skip J Cs i | i \<in> I]] { (interp_assert Iv) }"
  proof (intro allI ballI impI relational_hyper_hoare_tripleI)
    fix J S
    assume asm: "conj (interp_assert Iv) (conj (holds_for_prog_set J bs) (if J = I then (\<lambda>S. True) else (\<lambda>S. False))) S"
    have "J = I" 
    proof (rule ccontr)
      assume "J \<noteq> I"
      with asm show False
        by(auto simp add:conj_def)
    qed
    with asm assms(1) have "(interp_assert Iv)  (sem_lifted (map_comprehension Cs (\<lambda>i. i \<in> I)) S)"
      unfolding relational_hyper_hoare_triple_def conj_def
      by (simp add: holds_for_prog_set_def)
    moreover from \<open>J = I\<close> have "(map_comprehension (prog_set_or_skip J Cs) (\<lambda>i. i \<in> I)) = (map_comprehension Cs (\<lambda>i. i \<in> I))"
      by(auto simp add:map_comprehension_def prog_set_or_skip_def)
    ultimately show "interp_assert Iv (sem_lifted (map_comprehension (prog_set_or_skip J Cs) (\<lambda>i. i \<in> I)) S)"
      by (simp add: conj_def)
  qed
  from assms(2) have H2: "entails (interp_assert Iv) (can_step_any_unfinished I bs ?V)"
    unfolding entails_def low_exp_hyper_def
    by (smt (verit, del_insts) Pow_top conj_def holds_for_prog_set_def holds_forall_def holds_forall_hyper_def lnot_def)
  show ?thesis
  proof (intro relational_hyper_hoare_tripleI)
    fix S
    assume "interp_assert Iv S"
    with H1 H2 while_nonfixed_alignment[where ?Iv = "Iv" and ?I="I" and ?bs="bs" and V="?V" and ?Cs = "Cs"] 
      have "conj (loop_cond_assert bs Iv) (holds_forall_hyper I (lnot_hyper bs)) (sem_lifted [ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ] S)"
        by (simp add: relational_hyper_hoare_tripleE)
    with assms(2) show"conj (disj (interp_assert Iv) (hyper_emp I)) (holds_forall_hyper I (lnot_hyper bs))
                      (sem_lifted [i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I] S)" 
      apply(auto simp add:entails_def conj_def disj_def low_exp_hyper_def)*)

(*
theorem while_nonfixed_alignment2:
  assumes   "\<forall>J\<in>(Pow I - {{}}). \<Turnstile> { conj Iv (conj (holds_for_prog_set J bs) (V J))} [[i \<mapsto> prog_set_or_skip J Cs i | i \<in> I]] { Iv }"
      and   "entails Iv (can_step_any_unfinished I bs V)"
    shows   "\<Turnstile> { Iv } [[ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ]] { conj (if_terminates Iv) (holds_forall_hyper I (lnot_hyper bs))}"
  sorry*)



abbreviation all_unfinished_can_be_stepped_after where
"all_unfinished_can_be_stepped_after n Iv I bs V S \<equiv> (\<forall>i\<in>I. \<exists>n'\<ge>n.(entails (Iv n') (\<lambda>S. \<not>(holds_forall (lnot (bs i)) (S i)) \<longrightarrow> (\<exists>J\<in>(Pow I). i\<in>J \<and> (conj (holds_for_prog_set J bs) (V J) S)))))" 

thm relational_upwards_closed_def

(*theorem while_nonfixed_alignment4:
  assumes   "\<forall>n. \<forall>J\<in>(Pow I - {{}}). \<Turnstile> { conj (Iv n) (conj (holds_for_prog_set J bs) (V J))} [[i \<mapsto> Cs i | i \<in> J]] { Iv (Suc n) }"
      and   "\<forall>n. entails (Iv n) (all_unfinished_can_be_stepped_after n Iv I bs V)"
      and   "\<forall>n. entails (Iv n) (can_step_subset_or_all_finished I bs V)"
      and   "\<forall>n. \<Turnstile> { (Iv n) } [[i \<mapsto> Assume (lnot (bs i)) | i \<in> I]] { Q }"
    shows   "\<Turnstile> { (Iv 0) } [[ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ]] { conj Q (holds_forall_hyper I (lnot_hyper bs))}"
sorry
*)

abbreviation all_unfinished_can_be_stepped_after2 where
"all_unfinished_can_be_stepped_after2 n Iv I bs V S \<equiv> (\<forall>i\<in>I. \<exists>n'\<ge>n.(entails (Iv n') (\<lambda>S. \<not>(holds_forall (lnot (bs i)) (S i)) \<longrightarrow> (\<exists>J\<in>(Pow I). i\<in>J \<and> ((V J) S)))))" 

abbreviation can_step_subset_or_all_finished2 where
"can_step_subset_or_all_finished2 I bs V \<equiv> (disj (disj_I (Pow I - {{}}) (\<lambda>J. V J)) (holds_forall_hyper I (lnot_hyper bs)))"


fun sem_lifted_stacked where
"sem_lifted_stacked bs Cs S Js 0 = S" |
"sem_lifted_stacked bs Cs S Js (Suc n) = sem_lifted [i \<mapsto> if_then (bs i) (Cs i) | i \<in> Js (Suc n)] (sem_lifted_stacked bs Cs S Js n)"


theorem while_nonfixed_alignment6:
  assumes   "\<forall>n. \<forall>J\<in>(Pow I - {{}}). \<Turnstile> { conj (Iv n) (V J)} [[i \<mapsto> if_then (bs i) (Cs i) | i \<in> J]] { Iv (Suc n) }"
      and   "\<forall>n. entails (Iv n) (all_unfinished_can_be_stepped_after2 n Iv I bs V)"
      and   "\<forall>n. entails (Iv n) (can_step_subset_or_all_finished2 I bs V)"
      and   "\<forall>n. \<Turnstile> { (Iv n) } [[i \<mapsto> Assume (lnot (bs i)) | i \<in> I]] { Q n }"
      and   "relational_upwards_closed I Q Q_inf"
    shows   "\<Turnstile> { (Iv 0) } [[ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ]] { conj Q_inf (holds_forall_hyper I (lnot_hyper bs))}"
proof(intro relational_hyper_hoare_tripleI)
  fix S
  assume "Iv 0 S"
  let ?Ss = "sem_lifted_stacked bs Cs S"
  let ?Ss' = "\<lambda>Js. \<lambda>n. sem_lifted [i \<mapsto> Assume (lnot (bs i)) | i \<in> I] (?Ss Js n)"

  have "\<exists>Js::nat \<Rightarrow> nat set. (\<forall>n::nat. (Js n) \<in> (Pow I - {{}})) \<and> 
        (\<forall>n::nat. (Iv n) (?Ss Js n) \<and> ((V (Js (Suc n))) (?Ss Js n) \<or> holds_forall_hyper I (lnot_hyper bs) (?Ss Js n))) \<and>
        sem_lifted [ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ] S = hyper_union (?Ss' Js)" 
    sorry
  from this obtain Js where js_org:"(\<forall>n::nat. (Js n) \<in> (Pow I - {{}}))" and 
        ss_prop:"(\<forall>n::nat. (Iv n) (?Ss Js n) \<and> ((V (Js (Suc n))) (?Ss Js n) \<or> holds_forall_hyper I (lnot_hyper bs) (?Ss Js n)))" and
        wh_un: "sem_lifted [ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ] S = hyper_union (?Ss' Js)" by blast
  have q_ss': "\<forall>n::nat. (Q n) (?Ss' Js n)" 
  proof
    fix n
    from ss_prop have "(Iv n) (?Ss Js n)" by auto
    with assms(4) show "(Q n) (?Ss' Js n)" unfolding relational_hyper_hoare_triple_def by auto
  qed
  have hasc_ss':"hyper_ascending I (?Ss' Js)" 
  proof(intro hyper_ascendingI hyper_set_leI)
    fix n i
    assume "i\<in>I"
    show "sem_lifted (map_comprehension (\<lambda>i. Assume (lnot (bs i))) (\<lambda>i. i \<in> I)) (sem_lifted_stacked bs Cs S Js n) i
           \<subseteq> sem_lifted (map_comprehension (\<lambda>i. Assume (lnot (bs i))) (\<lambda>i. i \<in> I)) (sem_lifted_stacked bs Cs S Js (Suc n)) i"
      apply(auto simp add:sem_lifted_def sem_def map_comprehension_def lnot_def if_then_def)
       apply (metis SemAssume SemIf2 lnot_def)
      using \<open>i \<in> I\<close> by auto
  next
    fix n i
    assume "i \<notin> I"
    show "sem_lifted (map_comprehension (\<lambda>i. Assume (lnot (bs i))) (\<lambda>i. i \<in> I)) (sem_lifted_stacked bs Cs S Js n) i =
           sem_lifted (map_comprehension (\<lambda>i. Assume (lnot (bs i))) (\<lambda>i. i \<in> I)) (sem_lifted_stacked bs Cs S Js (Suc n)) i"
      using \<open>i \<notin> I\<close> js_org
      by(auto simp add:sem_lifted_def map_comprehension_def sem_def)
  qed
  from q_ss' hasc_ss' assms(5) have qinf_un: "Q_inf (hyper_union (?Ss' Js))" 
    unfolding relational_upwards_closed_def by simp
  have hfa_wh: "(holds_forall_hyper I (lnot_hyper bs)) (sem_lifted [ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ] S)" 
  unfolding while_cond_def
    by(auto simp add:sem_lifted_def holds_forall_hyper_def lnot_hyper_def lnot_def map_comprehension_def sem_def)
  from wh_un qinf_un hfa_wh show "(conj Q_inf (holds_forall_hyper I (lnot_hyper bs))) (sem_lifted [ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ] S)"
    by (simp add: conj_def)
qed

theorem while_nonfixed_alignment5:
  assumes   "\<forall>n. \<forall>J\<in>(Pow I - {{}}). \<Turnstile> { conj (Iv n) (conj (holds_for_prog_set J bs) (V J))} [[i \<mapsto> Cs i | i \<in> J]] { Iv (Suc n) }"
      and   "\<forall>n. entails (Iv n) (all_unfinished_can_be_stepped_after n Iv I bs V)"
      and   "\<forall>n. entails (Iv n) (can_step_subset_or_all_finished I bs V)"
      and   "\<forall>n. \<Turnstile> { (Iv n) } [[i \<mapsto> Assume (lnot (bs i)) | i \<in> I]] { Q n }"
      and   "relational_upwards_closed I Q Q_inf"
    shows   "\<Turnstile> { (Iv 0) } [[ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ]] { conj Q_inf (holds_forall_hyper I (lnot_hyper bs))}"
proof -
  let ?V' = "\<lambda>J. conj (holds_for_prog_set J bs) (V J)"
  have "\<forall>n. \<forall>J\<in>(Pow I - {{}}). \<Turnstile> { conj (Iv n) (?V' J)} [[i \<mapsto> if_then (bs i) (Cs i) | i \<in> J]] { Iv (Suc n) }"
  proof (intro allI ballI relational_hyper_hoare_tripleI)
    fix n J S
    assume asm1: "J \<in> Pow I - {{}}"
    assume asm2: "Logic.conj (Iv n) (Logic.conj (holds_for_prog_set J bs) (V J)) S"
    with asm1 asm2 assms(1) have H:"Iv (Suc n) (sem_lifted [i \<mapsto> Cs i | i \<in> J] S)" 
      unfolding relational_hyper_hoare_triple_def
      by blast
    have "(sem_lifted [i \<mapsto> if_then (bs i) (Cs i) | i \<in> J] S) = (sem_lifted [i \<mapsto> Cs i | i \<in> J] S)"
      apply(rule)
      using asm2
      apply(auto simp add:sem_lifted_def map_comprehension_def sem_def if_then_def lnot_def conj_def holds_for_prog_set_def holds_forall_hyper_def)
       apply fastforce
      by (metis SemAssume SemIf1 SemSeq snd_conv)
    with H show "Iv (Suc n) (sem_lifted [i \<mapsto> if_then (bs i) (Cs i) | i \<in> J] S)" by auto
  qed
  moreover have "\<forall>n. entails (Iv n) (all_unfinished_can_be_stepped_after2 n Iv I bs ?V')" using assms(2) by simp
  moreover have "\<forall>n. entails (Iv n) (can_step_subset_or_all_finished2 I bs ?V')" using assms(3) by simp
  ultimately show ?thesis using assms while_nonfixed_alignment6[where ?V="?V'"] by auto
qed


text\<open>Generalization of the conditional alignment rule from the Relational Decomposition paper to infinitely many programs.
      The rule assumes:
        a.	one lockstep case for every possible subset of programs
    It is a stronger generalization compared to the next one and the next one should be implied by it.\<close>
theorem while_nonfixed_alignment3:
  assumes   "\<forall>J\<in>(Pow I - {{}}). \<Turnstile> { conj Iv (conj (holds_for_prog_set J bs) (V J))} [[i \<mapsto> Cs i | i \<in> J]] { Iv }"
      and   "entails Iv (can_step_any_unfinished I bs V)"
      and   "\<Turnstile> { Iv } [[i \<mapsto> Assume (lnot (bs i)) | i \<in> I]] { Q }"
      and   "relational_upwards_closed I (\<lambda>n. Q) Q"
    shows   "\<Turnstile> { Iv } [[ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ]] { conj Q (holds_forall_hyper I (lnot_hyper bs))}"
proof -
  let ?Iv' = "\<lambda>n::nat. Iv"
  let ?Q' = "\<lambda>n. Q"
  from assms(1) have "\<And>n. \<forall>J\<in>(Pow I - {{}}). \<Turnstile> { conj (?Iv' n) (conj (holds_for_prog_set J bs) (V J))} [[i \<mapsto>  Cs i | i \<in> J]] { ?Iv' (Suc n) }"
    by simp
  moreover from assms(2) can_step_any_unfinished_can_step_subset_or_all_finished 
      have  "\<And>n. entails (?Iv' n) (can_step_subset_or_all_finished I bs V)"
        by blast
  moreover from assms(2) have "\<And>n. entails (?Iv' n) (all_unfinished_can_be_stepped_after n ?Iv' I bs V)"
        by (smt (verit, del_insts) entailsE entailsI order_refl)
  moreover from assms(3) have "\<And>n. \<Turnstile> { (?Iv' n) } [[i \<mapsto> Assume (lnot (bs i)) | i \<in> I]] { ?Q' n }"
    by auto
  moreover from assms(4) have "relational_upwards_closed I ?Q' Q" by blast
  ultimately show ?thesis using while_nonfixed_alignment5[where Iv = "?Iv'" and ?I="I" and ?bs="bs" and ?V="V" and ?Cs="Cs" and ?Q="?Q'" and ?Q_inf = "Q"]
    by blast
qed


text\<open>This is a weakened copy of while_lockstep rule from the fixed alignment rules section. 
      However, now it is proven using solely while_nonfixed_alignment3.\<close>
theorem while_lockstep_weaker:
  assumes "\<Turnstile> { conj Iv (holds_forall_hyper I bs) } [[i \<mapsto> (Cs i) | i \<in> I]] { conj Iv (low_exp_hyper I bs)}"
      and   "relational_upwards_closed I (\<lambda>n. disj Iv (hyper_emp I)) (disj Iv (hyper_emp I))"
    shows   "\<Turnstile> { conj Iv (low_exp_hyper I bs)} [[ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ]] { conj (disj Iv (hyper_emp I)) (holds_forall_hyper I (lnot_hyper bs))}"
proof -
  let ?V = "\<lambda>J. if J = I then (\<lambda>S. True) else (\<lambda>S. False)"
  let ?Iv = "conj Iv (low_exp_hyper I bs)"
  let ?Q = "disj Iv (hyper_emp I)"
  have H1: "\<forall>J\<in>(Pow I - {{}}). \<Turnstile> { conj ?Iv (conj (holds_for_prog_set J bs) (?V J))} [[i \<mapsto>  Cs i | i \<in> J]] { ?Iv }"
  proof (intro allI ballI impI relational_hyper_hoare_tripleI)
    fix J S
    assume asm: "conj ?Iv (conj (holds_for_prog_set J bs) (if J = I then (\<lambda>S. True) else (\<lambda>S. False))) S"
    have "J = I" 
    proof (rule ccontr)
      assume "J \<noteq> I"
      with asm show False
        by(auto simp add:conj_def)
    qed
    with asm assms(1) have "conj Iv (low_exp_hyper I bs) (sem_lifted (map_comprehension Cs (\<lambda>i. i \<in> I)) S)"
      unfolding relational_hyper_hoare_triple_def conj_def
      by (simp add: holds_for_prog_set_def)
    moreover from \<open>J = I\<close> have "[i \<mapsto>  Cs i | i \<in> J] = (map_comprehension Cs (\<lambda>i. i \<in> I))"
      by(auto simp add:map_comprehension_def)
    ultimately show "?Iv (sem_lifted [i \<mapsto>  Cs i | i \<in> J] S)"
      by (simp add: conj_def)
  qed
  have H2: "entails ?Iv (can_step_any_unfinished I bs ?V)"
    unfolding entails_def low_exp_hyper_def
    by (smt (verit, del_insts) Pow_top conj_def holds_for_prog_set_def holds_forall_def holds_forall_hyper_def lnot_def)
  have H3: "\<Turnstile> { ?Iv } [[i \<mapsto> Assume (lnot (bs i)) | i \<in> I]] { disj Iv (hyper_emp I) }" 
  proof (intro relational_hyper_hoare_tripleI)
    fix S
    assume "conj Iv (low_exp_hyper I bs) S"
    hence "Iv S" and "(low_exp_hyper I bs) S" 
      by (auto simp add: conj_def)
    hence "holds_forall_hyper I bs S \<or> holds_forall_hyper I (lnot_hyper bs) S "
      by (simp add: low_exp_either)
    thus "disj Iv (hyper_emp I) (sem_lifted [i \<mapsto> Assume (lnot (bs i)) | i \<in> I] S)"
    proof
      assume asm: "holds_forall_hyper I bs S"
      have "(sem_lifted [i \<mapsto> Assume (lnot (bs i)) | i \<in> I] S) = (\<lambda>i.(if (i\<in>I) then {} else S i))"
        apply(rule)
        using asm
        apply(auto simp add:holds_forall_hyper_def map_comprehension_def sem_lifted_def sem_def lnot_def)
        by fastforce
      moreover have "(hyper_emp I) (\<lambda>i.(if (i\<in>I) then {} else S i))"
        by(auto simp add:hyper_emp_def)
      ultimately have "(hyper_emp I) (sem_lifted [i \<mapsto> Assume (lnot (bs i)) | i \<in> I] S)" by auto
      thus ?thesis 
        by (simp add: disj_def)
    next
      assume asm: "holds_forall_hyper I (lnot_hyper bs) S"
      have "(sem_lifted [i \<mapsto> Assume (lnot (bs i)) | i \<in> I] S) = S"
        apply(rule)
        using asm
        apply(auto simp add:sem_lifted_def map_comprehension_def sem_def holds_forall_hyper_def lnot_hyper_def)
        by (metis SemAssume lnot_def sndI)
      with \<open>Iv S\<close> show ?thesis
        by (simp add: disj_def)
    qed
  qed
  show ?thesis
  proof (intro relational_hyper_hoare_tripleI)
    fix S
    assume "conj Iv (low_exp_hyper I bs) S"
    with H1 H2 H3 assms(2) while_nonfixed_alignment3[of "I" "?Iv" "bs"  "?V"  "Cs" "?Q"] 
      show "conj (disj Iv (hyper_emp I)) (holds_forall_hyper I (lnot_hyper bs)) (sem_lifted [ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ] S)"
        by (simp add: relational_hyper_hoare_tripleE)
  qed
qed

abbreviation can_step_or_all_finished where
"can_step_or_all_finished I bs U V \<equiv> (disj (disj (conj (holds_forall_hyper I bs) U) (disj_I I (\<lambda>j. conj (holds_for_prog j bs) (V j)))) (holds_forall_hyper I (lnot_hyper bs)))"

abbreviation can_step_any_unfinished' where
"can_step_any_unfinished' I bs U V S \<equiv> (\<forall>i\<in>I. \<not>(holds_forall (lnot (bs i)) (S i)) \<longrightarrow> ((conj (holds_forall_hyper I bs) U) S) \<or> (conj (holds_for_prog i bs) (V i) S))"


text\<open>Generalization of the conditional alignment rule from the Relational Decomposition paper to infinitely many programs.
      The rule assumes:
        a.	one lockstep case for all programs
        b.	one case for only a single program for any possible program
    It is a weaker generalization compared to the previous one.
    It is indeed proven by only using while_nonfixed_alignment3.\<close>
theorem while_nonfixed_alignment_single:
  assumes "\<Turnstile> { conj Iv (conj (holds_forall_hyper I bs) U)} [[i \<mapsto> Cs i | i \<in> I]] { Iv }" 
    and   "\<forall>j\<in>I. \<Turnstile> { conj Iv (conj (holds_for_prog j bs) (V j))} [[j \<mapsto> Cs j]] { Iv }"
    and   "entails Iv (can_step_any_unfinished' I bs U V)"
    and   "\<Turnstile> { Iv } [[i \<mapsto> Assume (lnot (bs i)) | i \<in> I]] { Q }"
    and   "relational_upwards_closed I (\<lambda>n. Q) Q"
    shows "\<Turnstile> { Iv } [[ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ]] { conj Q (holds_forall_hyper I (lnot_hyper bs))}"
proof - 
  have "card I = 1 \<or> card I \<noteq> 1" by auto
  thus ?thesis
  proof 
    assume asm0: "card I = 1"
    let ?V' = "\<lambda>J. disj (\<lambda>S. (\<forall>i\<in>J. V i S)) U"
    have "\<forall>J\<in>(Pow I - {{}}). \<Turnstile> { conj Iv (conj (holds_for_prog_set J bs) (?V' J))} [[i \<mapsto>  Cs i | i \<in> J]] { Iv }"
    proof (intro allI ballI)
      fix J
      assume asm: "J \<in> (Pow I - {{}})"
      with asm0 asm have "(\<exists>i. J = {i})"
        by (metis Diff_iff Pow_iff card_1_singletonE singleton_iff subset_singleton_iff)
      from this obtain j where asm2: "J = {j}" by auto
      have "j\<in>I"
        using asm asm2 by auto
      show "\<Turnstile> { conj Iv (conj (holds_for_prog_set J bs) (?V' J))} [[i \<mapsto>  Cs i | i \<in> J]] { Iv }"
      proof (intro relational_hyper_hoare_tripleI)
        fix S
        assume asm: "conj Iv (conj (holds_for_prog_set J bs) (?V' J)) S"
        hence "((\<forall>i\<in>J. V i S)) \<or> U S"
          by (simp add: conj_def disj_def)
        thus "Iv (sem_lifted [i \<mapsto>  Cs i | i \<in> J] S) "
        proof
          assume "\<forall>i\<in>J. V i S"
          with asm2 have "V j S"
            by simp
          with asm have "conj Iv (conj (holds_for_prog j bs) (V j)) S"
            by (simp add: asm2 conj_def holds_for_prog_def holds_for_prog_set_def holds_forall_hyper_def)
          with assms(2) \<open>j\<in>I\<close> have "Iv (sem_lifted [j \<mapsto> Cs j] S)"
            using relational_hyper_hoare_tripleE by blast
          moreover have "(sem_lifted [j \<mapsto> Cs j] S) = sem_lifted [i \<mapsto>  Cs i | i \<in> J] S"
            apply(rule) 
            using asm2 \<open>j\<in>I\<close>
            by(auto simp add:sem_lifted_def map_comprehension_def)
          ultimately show ?thesis 
            by simp
        next
          assume "U S"
          with asm have "conj Iv (conj (holds_forall_hyper I bs) U) S"
            by (metis (lifting) \<open>j \<in> I\<close> asm0 asm2 card_1_singletonE conj_def empty_iff holds_for_prog_set_def insert_iff)
          with assms(1) have "Iv (sem_lifted (map_comprehension Cs (\<lambda>i. i \<in> I)) S)"
            by (simp add: relational_hyper_hoare_triple_def)
          moreover have "(sem_lifted (map_comprehension Cs (\<lambda>i. i \<in> I)) S) = (sem_lifted (map_comprehension Cs (\<lambda>i. i \<in> J)) S)"
            apply(rule)
            using asm2 \<open>j\<in>I\<close>
            apply(auto simp add:sem_lifted_def map_comprehension_def)
            using asm0 card_1_singletonE apply blast
            using asm0 card_1_singletonE by blast
          ultimately show ?thesis  by auto
        qed
      qed
    qed
    moreover have "entails Iv (can_step_any_unfinished I bs ?V')" 
      unfolding entails_def 
    proof (intro allI impI ballI)
      fix S i
      assume "Iv S" and "i\<in>I" and "\<not> holds_forall (lnot (bs i)) (S i)"
      with assms(3) have "((conj (holds_forall_hyper I bs) U) S) \<or> (conj (holds_for_prog i bs) (V i) S)"
        using entailsE by fastforce
      thus "\<exists>J\<in>Pow I. i \<in> J \<and> ((conj (holds_for_prog_set J bs) (?V' J)) S)"
      proof
        assume asm: "Logic.conj (holds_forall_hyper I bs) U S"
        thus ?thesis
          by (metis (mono_tags, lifting) Pow_top \<open>i \<in> I\<close> conj_def disj_def holds_for_prog_set_def)
      next
        assume asm4: "conj (holds_for_prog i bs) (V i) S"
        with \<open>i\<in>I\<close> have "{i}\<in>Pow I \<and> i \<in> {i}" 
          by simp
        from asm4 have "conj (holds_for_prog_set {i} bs) (?V' {i}) S" 
          by(auto simp add:conj_def holds_for_prog_def holds_for_prog_set_def holds_forall_hyper_def disj_def)
        thus ?thesis 
          using \<open>{i} \<in> Pow I \<and> i \<in> {i}\<close> by blast 
      qed
    qed
    ultimately show ?thesis using assms(4) assms(5) while_nonfixed_alignment3[where ?Iv = "Iv" and ?I="I" and ?bs="bs" and V="\<lambda>J. disj (\<lambda>S. (\<forall>i\<in>J. V i S)) U" and ?Cs="Cs" and ?Q="Q"]
      by blast
  next
    assume asm0: "card I \<noteq> 1"
    let ?V' = "\<lambda>J. if (J = I) then U else (if (card J = 1) then (\<lambda>S. (\<forall>i\<in>J. V i S)) else (\<lambda>S. False))"
    have "\<forall>J\<in>(Pow I - {{}}). \<Turnstile> { conj Iv (conj (holds_for_prog_set J bs) (?V' J))} [[i \<mapsto>  Cs i | i \<in> J]] { Iv }"
    proof (intro allI ballI)
      fix J
      assume asm: "J \<in> (Pow I - {{}})"
      with asm have "((J = I) \<or> (J \<noteq> I \<and> (\<exists>i. J = {i})) \<or> (J \<noteq> I \<and> (card J \<noteq> 1)))"
        by (meson card_1_singletonE)
      then show "\<Turnstile> { conj Iv (conj (holds_for_prog_set J bs) (?V' J))} [[i \<mapsto>  Cs i | i \<in> J]] { Iv }"
      proof (rule)
        assume asm1: "((J = I))"
        from asm1 have "conj Iv (conj (holds_for_prog_set J bs) (?V' J)) = conj Iv (conj (holds_forall_hyper I bs) U)"
          by (simp add: holds_for_prog_set_def)
        moreover from asm1 have "[i \<mapsto> Cs i | i \<in> I] = [i \<mapsto>  Cs i | i \<in> J]"
          apply(rule)
          by(auto simp add:map_comprehension_def asm1)
        ultimately show ?thesis using assms(1)
          by (simp add: relational_hyper_hoare_triple_def)
      next
        assume "(J \<noteq> I \<and> (\<exists>i. J = {i})) \<or> J \<noteq> I \<and> card J \<noteq> 1"
        thus ?thesis
        proof
          assume "(J \<noteq> I \<and> (\<exists>i. J = {i}))"
          from this obtain j where asm2: "J \<noteq> I \<and> J = {j}" by auto
          have "conj Iv (conj (holds_for_prog_set J bs) (?V' J)) = conj Iv (conj (holds_for_prog j bs) (V j))" using asm2
            by(auto simp add:holds_for_prog_set_def holds_for_prog_def asm2 conj_def holds_forall_hyper_def)
          moreover from asm2 have "[j \<mapsto> Cs j] = [i \<mapsto>  Cs i | i \<in> J]"
            apply(rule)
            by(auto simp add:map_comprehension_def asm2)
          ultimately show ?thesis
            using asm asm2 assms(2) by auto
        next
          assume "J \<noteq> I \<and> card J \<noteq> 1"
          thus ?thesis
            by (simp add: conj_def relational_hyper_hoare_triple_def)
        qed
      qed
    qed
    moreover have "entails Iv (can_step_any_unfinished I bs ?V')" 
      unfolding entails_def 
    proof (intro allI impI ballI)
      fix S i
      assume "Iv S" and "i\<in>I" and "\<not> holds_forall (lnot (bs i)) (S i)"
      with assms(3) have "((conj (holds_forall_hyper I bs) U) S) \<or> (conj (holds_for_prog i bs) (V i) S)"
        using entailsE by fastforce
      thus "\<exists>J\<in>Pow I. i \<in> J \<and> ((conj (holds_for_prog_set J bs) (?V' J)) S)"
      proof
        assume asm: "Logic.conj (holds_forall_hyper I bs) U S"
        thus ?thesis
          by (smt (verit, ccfv_SIG) Pow_top \<open>i \<in> I\<close> holds_for_prog_set_def)
      next
        assume asm4: "conj (holds_for_prog i bs) (V i) S"
        with \<open>i\<in>I\<close> have "{i}\<in>Pow I \<and> i \<in> {i}" 
          by simp
        from asm4 have "conj (holds_for_prog_set {i} bs) (?V' {i}) S"
          using asm0
          by(auto simp add:conj_def holds_for_prog_def holds_for_prog_set_def holds_forall_hyper_def)
        thus ?thesis 
          using \<open>{i} \<in> Pow I \<and> i \<in> {i}\<close> by blast 
      qed
    qed
    ultimately show ?thesis using assms(4) assms(5) while_nonfixed_alignment3[where ?Iv = "Iv" and ?I="I" and ?bs="bs" and V="\<lambda>J. if J = I then U else (if (card J = 1) then (\<lambda>S. (\<forall>i\<in>J. V i S)) else (\<lambda>S. False))" and ?Cs="Cs" and ?Q="Q"]
      by blast
  qed
qed



section \<open>Single sem usage simplification rules\<close>

lemma single_sem_eq_fin:
  assumes "\<langle>C, \<sigma>\<rangle> \<rightarrow> \<sigma>0'" and "\<sigma>0' = \<sigma>'"
  shows "\<langle>C, \<sigma>\<rangle> \<rightarrow> \<sigma>'"
  using assms by simp


lemma single_sem_eq_init:
  assumes "\<langle>C, \<sigma>0\<rangle> \<rightarrow> \<sigma>'" and "\<sigma>0 = \<sigma>"
  shows "\<langle>C, \<sigma>\<rangle> \<rightarrow> \<sigma>'"
  using assms by simp


section \<open>LHC's subsumed rules\<close>

subsection \<open>Hyper-structure rules\<close>

text\<open>definition of relevant indices of a hyper-assertion adapted from LHC\<close>
definition idx :: "'a rel_hyper_assertion \<Rightarrow> nat set" where
"idx P = UNIV - {(i::nat). (\<forall>Ss S. (P Ss) \<longleftrightarrow> (P (Ss(i := S))))}"


lemma idxE: "\<And>i. (i \<notin> idx P) \<Longrightarrow> (\<forall>Ss S. (P Ss) \<longleftrightarrow> (P (Ss(i := S))))"
  unfolding idx_def
  by simp


definition irl_idcs :: "'a rel_hyper_assertion \<Rightarrow> nat set set" where
"irl_idcs P = {I. (\<forall>Ss Ss'. (P Ss) \<longleftrightarrow> (P (override_on Ss Ss' I)))}"


lemma map_add_com:
  assumes "\<forall>i \<in> (dom Cs1) \<inter> (dom Cs2). Cs1 i = Cs2 i"
  shows "(Cs1 ++ Cs2) = (Cs2 ++ Cs1)"
  by (metis (full_types) IntI assms map_add_dom_app_simps(3) map_le_def map_le_iff_map_add_commute map_le_map_add)


lemma conj_rule_main:
  assumes "((dom Cs2) - (dom Cs1)) \<in> irl_idcs Q1"
      and "Q1 (sem_lifted Cs1 S)"
    shows "Q1 (sem_lifted (Cs2 ++ Cs1) S)"
proof -
  have H: "\<forall>i\<in>(UNIV - ((dom Cs2) - (dom Cs1))). (sem_lifted (Cs2 ++ Cs1) S) i = (sem_lifted Cs1 S) i"
    by (metis Diff_iff map_add_dom_app_simps(1,2) sem_lifted_def)
  have "\<forall>i\<in>((dom Cs2) - (dom Cs1)). (sem_lifted (Cs2 ++ Cs1) S) i = (sem_lifted Cs2 S) i"
    by (simp add: map_add_dom_app_simps(3) sem_lifted_def)
  let ?ff = "(override_on (sem_lifted Cs1 S) (sem_lifted (Cs2 ++ Cs1) S) (dom Cs2 - dom Cs1))"
  have H2: "?ff = (sem_lifted (Cs2 ++ Cs1) S)" 
  proof
    fix i 
    from H show "override_on (sem_lifted Cs1 S) (sem_lifted (Cs2 ++ Cs1) S) (dom Cs2 - dom Cs1) i = sem_lifted (Cs2 ++ Cs1) S i"
      by (metis DiffI UNIV_I override_on_apply_in override_on_apply_notin)
  qed
  have "(Q1 (sem_lifted Cs1 S) \<longleftrightarrow> Q1 (override_on (sem_lifted Cs1 S) (sem_lifted (Cs2 ++ Cs1) S) (dom Cs2 - dom Cs1)))" using assms(1)
    by (simp add: irl_idcs_def)
  with assms(2) have "Q1 ?ff" by auto
  with H2 show ?thesis by auto
qed

text\<open>The generalized version of wp-conj\<close>
theorem conj_rule:
  assumes "\<Turnstile> {P} [Cs1] {Q1}"
      and "\<Turnstile> {P} [Cs2] {Q2}"
      and "((dom Cs2) - (dom Cs1)) \<in> irl_idcs Q1"
      and "((dom Cs1) - (dom Cs2)) \<in> irl_idcs Q2"
      and "\<forall>i \<in> (dom Cs1) \<inter> (dom Cs2). Cs1 i = Cs2 i"
    shows "\<Turnstile> {P} [Cs1 ++ Cs2] {conj Q1 Q2}"
proof (rule relational_hyper_hoare_tripleI)
  fix S 
  assume "P S"
  from \<open>P S\<close> assms(1) relational_hyper_hoare_tripleE have H1: "Q1 (sem_lifted (Cs1) S)" by auto
  from \<open>P S\<close> assms(2) relational_hyper_hoare_tripleE have H2: "Q2 (sem_lifted (Cs2) S)" by auto
  from map_add_com conj_rule_main H1 assms(3,5) have "Q1 (sem_lifted (Cs1 ++ Cs2) S)" by metis
  moreover from conj_rule_main H2 assms(4,5) have "Q2 (sem_lifted (Cs1 ++ Cs2) S)" by metis  
  ultimately show "conj Q1 Q2 (sem_lifted (Cs1 ++ Cs2) S)" unfolding conj_def by auto
qed


definition wp_RHHL :: "'a hyper_program \<Rightarrow> 'a rel_hyper_assertion \<Rightarrow> 'a rel_hyper_assertion" where
"wp_RHHL Cs Q = (\<lambda>S. (Q (sem_lifted Cs S)))"


lemma wp_RHHL_E: 
  assumes "wp_RHHL Cs Q S"
  shows "(Q (sem_lifted Cs S))"
  using assms unfolding wp_RHHL_def
  by simp

lemma wp_RHHL_I: 
  assumes "(Q (sem_lifted Cs S))"
  shows "wp_RHHL Cs Q S"
  using assms unfolding wp_RHHL_def
  by simp

text\<open>The generalized version of the right-to-left direction of wp-nest\<close>
theorem split_rule:
  assumes "\<Turnstile> { P } [ Cs ++ Cs' ] { Q }"
      and "dom Cs \<inter> dom Cs' = {}"
    shows "\<Turnstile> { P } [ Cs ] { wp_RHHL Cs' Q } \<and> \<Turnstile> { wp_RHHL Cs' Q } [ Cs' ] { Q }"
proof
  show "\<Turnstile> {P} [Cs] {wp_RHHL Cs' Q}"
  proof (rule relational_hyper_hoare_tripleI)
    fix S
    assume "P S"
    with assms(1) have "Q (sem_lifted (Cs ++ Cs') S)"
      by (simp add: relational_hyper_hoare_triple_def)
    with assms(2) sem_lifted_on_disjoint_maps_seq have "Q (sem_lifted Cs' (sem_lifted Cs S))" 
      by metis
    thus "wp_RHHL Cs' Q (sem_lifted Cs S)"
      by (simp add: wp_RHHL_I)
  qed
next
  show "\<Turnstile> {wp_RHHL Cs' Q} [Cs'] {Q}"
    by (simp add: relational_hyper_hoare_tripleI wp_RHHL_def)
qed

(*
definition single_sem_exists 
  ("\<langle>_, _\<rangle>\<rightarrow>" [51,0] 81) where
"\<langle>C, \<sigma>\<rangle>\<rightarrow> = (\<exists>\<sigma>'. \<langle>C, \<sigma>\<rangle> \<rightarrow> \<sigma>')"


text\<open>definition of relevant indices of a hyper-assertion adapted from LHC\<close>
definition proj :: "'a hyper_program \<Rightarrow> 'a rel_hyper_assertion" where
"proj Cs = (\<lambda>S. \<forall>i. (case (Cs i) of None \<Rightarrow> True | Some C \<Rightarrow> (\<forall>(l, \<sigma>)\<in>(S i). \<exists>\<sigma>'. \<langle>C, \<sigma>\<rangle> \<rightarrow> \<sigma>')))"
*)

definition project_out :: "nat set \<Rightarrow> 'a rel_hyper_assertion \<Rightarrow> 'a rel_hyper_assertion" where
"project_out I P Ss = (\<exists>Ss'. P (override_on Ss Ss' I))"


lemma proj_rule_main:
  assumes "dom Cs \<inter> dom Cs' = {}"
  shows "(sem_lifted (Cs ++ Cs') (override_on S SCs (dom Cs))) = (override_on (sem_lifted Cs' S) (sem_lifted Cs SCs) (dom Cs))"
proof
  fix i 
  show "sem_lifted (Cs ++ Cs') (override_on S SCs (dom Cs)) i = override_on (sem_lifted Cs' S) (sem_lifted Cs SCs) (dom Cs) i"
    by (metis (mono_tags, lifting) assms map_add_comm map_add_dom_app_simps(1,3) override_on_def sem_lifted_def)
qed

text\<open>The generalized version of wp-proj\<close>
theorem proj_rule:
  assumes "\<Turnstile> { P } [ Cs ++ Cs' ] { Q }"
      and "dom Cs \<inter> dom Cs' = {}"
    shows "\<Turnstile> { project_out (dom Cs) P } [ Cs' ] { project_out (dom Cs) Q }"
proof (rule relational_hyper_hoare_tripleI)
  fix S
  assume "project_out (dom Cs) P S"
  from this obtain SCs where " P (override_on S SCs (dom Cs))"
    using project_out_def by blast
  with assms(1) have "Q (sem_lifted (Cs ++ Cs') (override_on S SCs (dom Cs)))"
    by (simp add: relational_hyper_hoare_tripleE)
  with proj_rule_main assms(2) have "(Q (override_on (sem_lifted Cs' S) (sem_lifted Cs SCs) (dom Cs)))" 
    by metis
  thus "project_out (dom Cs) Q (sem_lifted Cs' S)" 
    using project_out_def by auto
qed


subsection \<open>Reindexing rules\<close>

definition reindex_assertion where
"reindex_assertion \<pi> P S = P (reindex_hyper_stuff \<pi> S)"

abbreviation id_upd :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"  
("\<lparr>_ \<mapsto> _\<rparr>")
where
  "\<lparr>i \<mapsto> x\<rparr> \<equiv> id(i := x)"

lemma reindex_pass_main:
  assumes "i \<notin> (dom Cs) \<and> j \<notin> (dom Cs)"
  shows "(reindex_hyper_stuff \<lparr>j \<mapsto> i\<rparr> Cs) = Cs"
  unfolding reindex_hyper_stuff_def
proof(rule)
  from assms have H: "Cs i = None \<and> Cs j = None" by auto
  fix i'
  have "i' = j \<or> i' \<noteq> j" by auto
  thus "Cs (\<lparr>j \<mapsto> i\<rparr> i') = Cs i'"
  proof
    assume "i' = j"
    with H show "Cs (\<lparr>j \<mapsto> i\<rparr> i') = Cs i'" by simp
  next
    assume "i' \<noteq> j"
    thus  "Cs (\<lparr>j \<mapsto> i\<rparr> i') = Cs i'" by simp
  qed
qed


text\<open>The generalized version of wp-idx-pass\<close>
theorem reindex_pass:
  assumes "\<Turnstile> { P } [ Cs ] { Q }"
      and "i \<notin> (dom Cs) \<and> j \<notin> (dom Cs)"
    shows "\<Turnstile> { reindex_assertion \<lparr>j \<mapsto> i\<rparr> P} [ Cs ] { reindex_assertion \<lparr>j \<mapsto> i\<rparr> Q }"
proof (rule relational_hyper_hoare_tripleI)
  fix S
  assume "reindex_assertion \<lparr>j \<mapsto> i\<rparr> P S"
  hence "P (reindex_hyper_stuff \<lparr>j \<mapsto> i\<rparr> S)"
    by (simp add: reindex_assertion_def)
  with assms(1) have "Q (sem_lifted Cs (reindex_hyper_stuff \<lparr>j \<mapsto> i\<rparr> S))"
    by (simp add: relational_hyper_hoare_tripleE)
  with assms(2) reindex_pass_main have "Q (sem_lifted (reindex_hyper_stuff \<lparr>j \<mapsto> i\<rparr> Cs) (reindex_hyper_stuff \<lparr>j \<mapsto> i\<rparr> S))" 
    by metis
  hence "Q ((reindex_hyper_stuff \<lparr>j \<mapsto> i\<rparr>) (sem_lifted Cs S))"
    by (simp add: sem_lifted_reindex)
  thus "reindex_assertion \<lparr>j \<mapsto> i\<rparr> Q (sem_lifted Cs S)" 
    by (simp add: reindex_assertion_def)
qed

lemma reindex_merge_main:
  assumes "i \<notin> (dom Cs') \<and> j \<notin> (dom Cs')"
  shows "reindex_hyper_stuff \<lparr>j \<mapsto> i\<rparr> ([i \<mapsto> C] ++ Cs') = [i \<mapsto> C, j \<mapsto> C] ++ Cs'"
  unfolding reindex_hyper_stuff_def
proof (rule)
  fix i'
  have "i' = j \<or> i' \<noteq> j" by auto
  thus "([i \<mapsto> C] ++ Cs') (\<lparr>j \<mapsto> i\<rparr> i') = ([i \<mapsto> C, j \<mapsto> C] ++ Cs') i'"
  proof
    assume "i' = j"
    with assms show "([i \<mapsto> C] ++ Cs') (\<lparr>j \<mapsto> i\<rparr> i') = ([i \<mapsto> C, j \<mapsto> C] ++ Cs') i'"
      by (simp add: map_add_dom_app_simps(3))
  next
    assume "i' \<noteq> j"
    with assms show "([i \<mapsto> C] ++ Cs') (\<lparr>j \<mapsto> i\<rparr> i') = ([i \<mapsto> C, j \<mapsto> C] ++ Cs') i'"
      by (simp add: map_add_upd_left)
  qed
qed

text\<open>The generalized version of wp-idx-merge\<close>
theorem reindex_merge:
  assumes "\<Turnstile> { P } [ [i \<mapsto> C, j \<mapsto> C] ++ Cs' ] { Q } \<and> i \<notin> (dom Cs') \<and> j \<notin> (dom Cs')" 
    shows "\<Turnstile> { reindex_assertion \<lparr>j \<mapsto> i\<rparr> P} [ [i \<mapsto> C] ++ Cs' ] { reindex_assertion \<lparr>j \<mapsto> i\<rparr> Q }"
proof (rule relational_hyper_hoare_tripleI)
  fix S
  assume "reindex_assertion \<lparr>j \<mapsto> i\<rparr> P S"
  hence "P (reindex_hyper_stuff \<lparr>j \<mapsto> i\<rparr> S)"
    by (simp add: reindex_assertion_def)
  with assms(1) have "Q (sem_lifted ([i \<mapsto> C, j \<mapsto> C] ++ Cs') (reindex_hyper_stuff \<lparr>j \<mapsto> i\<rparr> S))"
    using relational_hyper_hoare_tripleE by blast
  with reindex_merge_main assms(1) have "Q (sem_lifted (reindex_hyper_stuff \<lparr>j \<mapsto> i\<rparr> ([i \<mapsto> C] ++ Cs')) (reindex_hyper_stuff \<lparr>j \<mapsto> i\<rparr> S))"
    by metis
  hence "Q (reindex_hyper_stuff \<lparr>j \<mapsto> i\<rparr> (sem_lifted ([i \<mapsto> C] ++ Cs' ) S))"
    by (simp add: sem_lifted_reindex)
  thus "reindex_assertion \<lparr>j \<mapsto> i\<rparr> Q (sem_lifted ([i \<mapsto> C] ++ Cs') S)" 
    by (simp add: reindex_assertion_def)
qed


lemma reindex_swap_main:
  assumes "i \<notin> (dom Cs') \<and> j \<notin> (dom Cs')"
  shows "\<forall>i' \<noteq> i. (reindex_hyper_stuff \<lparr>j \<mapsto> i\<rparr> ([i \<mapsto> C] ++ Cs') i') = (([j \<mapsto> C] ++ Cs') i')"
  unfolding reindex_hyper_stuff_def
proof (intro allI ballI impI)
  fix i'
  assume " i' \<noteq> i"
  have "i' = j \<or> i' \<noteq> j" by auto
  thus "([i \<mapsto> C] ++ Cs') (\<lparr>j \<mapsto> i\<rparr> i') = ([j \<mapsto> C] ++ Cs') i'"
  proof
    assume "i' = j"
    with assms show "([i \<mapsto> C] ++ Cs') (\<lparr>j \<mapsto> i\<rparr> i') = ([j \<mapsto> C] ++ Cs') i'"
      by (simp add: map_add_dom_app_simps(3))
  next
    assume "i' \<noteq> j"
    with assms show "([i \<mapsto> C] ++ Cs') (\<lparr>j \<mapsto> i\<rparr> i') = ([j \<mapsto> C] ++ Cs') i'"
      by (simp add: \<open>i' \<noteq> i\<close> map_add_upd_left)
  qed
qed


lemma reindex_swap_main2:
  assumes "\<forall>i' \<noteq> i. Cs1 i' = Cs2 i'"
      and "i \<notin> idx Q"
  shows "Q (sem_lifted Cs1 S) = Q (sem_lifted Cs2 S)"
proof -
  have "(sem_lifted Cs2 S) = (sem_lifted Cs1 S)(i := (sem_lifted Cs2 S) i)"
  proof
    fix j
    have "j = i \<or> j \<noteq> i" by auto
    thus "(sem_lifted Cs2 S) j = ((sem_lifted Cs1 S)(i := (sem_lifted Cs2 S) i)) j"
    proof
      assume "j = i"
      thus "sem_lifted Cs2 S j = ((sem_lifted Cs1 S)(i := sem_lifted Cs2 S i)) j"
        by simp
    next 
      assume "j \<noteq> i" 
      with assms(1) show "sem_lifted Cs2 S j = ((sem_lifted Cs1 S)(i := sem_lifted Cs2 S i)) j"
        by (simp add: sem_lifted_def)
    qed
  qed
  with assms(2) show "Q (sem_lifted Cs1 S) = Q (sem_lifted Cs2 S)" unfolding idx_def
    by (metis (mono_tags, lifting) UNIV_I mem_Collect_eq set_diff_eq)
qed


text\<open>The generalized version of wp-idx-swap\<close>
theorem reindex_swap:
  assumes "\<Turnstile> { P } [ [j \<mapsto> C] ++ Cs' ] { Q } \<and> j \<notin> (dom Cs')"
      and "i \<notin> (idx Q) \<and> i \<notin> (dom Cs')"
    shows "\<Turnstile> { reindex_assertion \<lparr>j \<mapsto> i\<rparr> P} [ [i \<mapsto> C] ++ Cs' ] { reindex_assertion \<lparr>j \<mapsto> i\<rparr> Q }"
proof (rule relational_hyper_hoare_tripleI)
  fix S
  assume "reindex_assertion \<lparr>j \<mapsto> i\<rparr> P S"
  hence "P (reindex_hyper_stuff \<lparr>j \<mapsto> i\<rparr> S)"
    by (simp add: reindex_assertion_def)
  with assms(1) have "Q (sem_lifted ([j \<mapsto> C] ++ Cs') (reindex_hyper_stuff \<lparr>j \<mapsto> i\<rparr> S))"
    using relational_hyper_hoare_tripleE by blast
  with assms reindex_swap_main reindex_swap_main2 
    have "Q (sem_lifted (reindex_hyper_stuff \<lparr>j \<mapsto> i\<rparr> ([i \<mapsto> C] ++ Cs')) (reindex_hyper_stuff \<lparr>j \<mapsto> i\<rparr> S))"
      by (smt (verit, ccfv_SIG))
  hence "Q (reindex_hyper_stuff \<lparr>j \<mapsto> i\<rparr> (sem_lifted ([i \<mapsto> C] ++ Cs' ) S))"
    by (simp add: sem_lifted_reindex)
  thus "reindex_assertion \<lparr>j \<mapsto> i\<rparr> Q (sem_lifted ([i \<mapsto> C] ++ Cs') S)" 
    by (simp add: reindex_assertion_def)
qed





lemma reindex_post_main:
  assumes "j \<notin> (dom Cs)"
  shows "let S' = (sem_lifted (reindex_hyper_stuff \<lparr>j \<mapsto> i\<rparr> Cs) S) in 
        (sem_lifted Cs (S(j := S' j))) = S'"
  unfolding Let_def
proof
  let ?S' = "(sem_lifted (reindex_hyper_stuff \<lparr>j \<mapsto> i\<rparr> Cs) S)"
  fix i'
  have "i' = j \<or> i' \<noteq> j" by auto
  thus "sem_lifted Cs (S(j := ?S' j)) i' = ?S' i'"
  proof
    assume "i' = j"
    thus "sem_lifted Cs (S(j := ?S' j)) i' = ?S' i'" unfolding sem_lifted_def
      using assms by fastforce
  next 
    assume "i' \<noteq> j"
    thus "sem_lifted Cs (S(j := ?S' j)) i' = ?S' i'" unfolding sem_lifted_def
      by (simp add: reindex_hyper_stuff_def)
  qed
qed




text\<open>The generalized version of wp-idx-post\<close>
theorem reindex_post:
  assumes "\<Turnstile> { P } [ Cs ] { Q }"
      and "j \<notin> (dom Cs) \<and> j \<notin> (idx P)"
    shows "\<Turnstile> { P } [ Cs ] { reindex_assertion \<lparr>j \<mapsto> i\<rparr> Q }"
proof (rule relational_hyper_hoare_tripleI)
  fix S
  let ?S' = "(sem_lifted (reindex_hyper_stuff \<lparr>j \<mapsto> i\<rparr> Cs) (reindex_hyper_stuff \<lparr>j \<mapsto> i\<rparr> S))"
  assume "P S"
  have "(reindex_hyper_stuff \<lparr>j \<mapsto> i\<rparr> S) = S(j:=(S i))" unfolding reindex_hyper_stuff_def
    by fastforce
  with \<open>P S\<close> assms(2) have "P (reindex_hyper_stuff \<lparr>j \<mapsto> i\<rparr> S)"
    using idxE by force
  with assms(2) have "P ((reindex_hyper_stuff \<lparr>j \<mapsto> i\<rparr> S)(j := ?S' j))"
    using idxE by blast
  with assms(1) have H: "Q (sem_lifted Cs ((reindex_hyper_stuff \<lparr>j \<mapsto> i\<rparr> S)(j := ?S' j)))"
    by (simp add: relational_hyper_hoare_tripleE)
  from assms(2) have "(sem_lifted Cs ((reindex_hyper_stuff \<lparr>j \<mapsto> i\<rparr> S)(j := ?S' j))) j = ?S' j" unfolding sem_lifted_def by force
  from reindex_post_main assms(2) H have "Q ?S'" by metis
  hence "Q ((reindex_hyper_stuff \<lparr>j \<mapsto> i\<rparr>) (sem_lifted Cs S))"
    by (simp add: sem_lifted_reindex)
  thus "reindex_assertion \<lparr>j \<mapsto> i\<rparr> Q (sem_lifted Cs S)" 
    by (simp add: reindex_assertion_def)
qed



subsection \<open>Lockstep rules\<close>


abbreviation assign_hyper_set where
"assign_hyper_set I Xs Es S \<equiv> (\<lambda>i. (if i \<in> I then { (l, \<sigma>((Xs i) := (Es i) \<sigma>)) |l \<sigma>. (l, \<sigma>) \<in> (S i) } else S i))"

abbreviation assign_prec where
"assign_prec P I Xs Es S \<equiv> P (assign_hyper_set I Xs Es S)"

theorem assign_lockstep:
  shows "\<Turnstile>  { assign_prec P I Xs Es} [[i \<mapsto> Assign (Xs i) (Es i) |i \<in> I]] {P}"
proof (rule relational_hyper_hoare_tripleI)
  fix S
  assume asm: "assign_prec P I Xs Es S"
  have "assign_hyper_set I Xs Es S = (sem_lifted [i \<mapsto> Assign (Xs i) (Es i) |i \<in> I] S)"
  proof
    fix i
    show "assign_hyper_set I Xs Es S i = (sem_lifted [i \<mapsto> Assign (Xs i) (Es i) |i \<in> I] S) i"
      by(auto simp add:sem_lifted_def map_comprehension_def sem_def intro:SemAssign)
  qed
  with asm show "P (sem_lifted [i \<mapsto> Assign (Xs i) (Es i) |i \<in> I] S)" by auto
qed

text\<open>The generalized version of the right-to-left direction of wp-seqI\<close>
theorem seq_split_rule:
  assumes "\<Turnstile> { P } [ hyper_seq Cs Cs' ] { Q }"
    shows "\<Turnstile> { P } [ Cs ] { wp_RHHL Cs' Q } \<and> \<Turnstile> { wp_RHHL Cs' Q } [ Cs' ] { Q }"
proof
  show "\<Turnstile> {P} [Cs] {wp_RHHL Cs' Q}"
  proof (rule relational_hyper_hoare_tripleI)
    fix S
    assume "P S"
    with assms(1) have "Q (sem_lifted (hyper_seq Cs Cs') S)"
      by (simp add: relational_hyper_hoare_triple_def)
    hence "Q (sem_lifted Cs' (sem_lifted Cs S))" 
      by (simp add: sem_lifted_hyper_seq)
    thus "wp_RHHL Cs' Q (sem_lifted Cs S)"
      by (simp add: wp_RHHL_I)
  qed
next
  show "\<Turnstile> {wp_RHHL Cs' Q} [Cs'] {Q}"
    by (simp add: relational_hyper_hoare_tripleI wp_RHHL_def)
qed


text\<open>Refinement relation between two hyper-programs. Satisfied if all corresponding programs
      are in the refinement relation.\<close>
definition refines_hyper_program :: "'a hyper_program \<Rightarrow> 'a hyper_program \<Rightarrow> bool"where
"refines_hyper_program Cs1 Cs2  = (\<forall>S. (\<forall>i. (sem_lifted Cs1 S) i \<subseteq> (sem_lifted Cs2 S) i))"




fun no_exists_state :: "'a syn_assertion \<Rightarrow> bool" where
"no_exists_state (AConst _) = True" |
"no_exists_state (AComp _ _ _) = True" |
"no_exists_state (AForallState _ A) = no_exists_state A" |
"no_exists_state (AExistsState _ _) = False" |
"no_exists_state (AForall A) = no_exists_state A" | 
"no_exists_state (AExists A) = no_exists_state A" |
"no_exists_state (AOr A1 A2) = ((no_exists_state A1) \<and> (no_exists_state A2))" |
"no_exists_state (AAnd A1 A2) = ((no_exists_state A1) \<and> (no_exists_state A2))"


lemma meta_refinement_rule_main:
  assumes "refines_hyper_program Cs1 Cs2"
      and "no_exists_state Q"
      and "sat_assertion vals states Q (sem_lifted Cs2 S)"
    shows "sat_assertion vals states Q (sem_lifted Cs1 S)"
proof -
  from assms(2) assms(3) show "sat_assertion vals states Q (sem_lifted Cs1 S)"
  proof (induction Q arbitrary:vals states)
    case (AConst x)
    then show ?case by simp
  next
    case (AComp x1a x2 x3)
    then show ?case by simp
  next
    case (AForallState x1a Q)
    then show ?case 
      by (meson assms(1) no_exists_state.simps(3) refines_hyper_program_def sat_assertion.simps(3) subset_iff)
  next
    case (AExistsState x1a Q)
    then show ?case 
      by auto
  next
    case (AForall Q)
    then show ?case 
      by simp
  next
    case (AExists Q)
    then show ?case by auto
  next
    case (AOr Q1 Q2)
    then show ?case by auto
  next
    case (AAnd Q1 Q2)
    then show ?case by auto
  qed
qed

text\<open>Modified version of the rewrite_rule inspired by LHC's wp-refine. 
    It uses meta reasoning about refinement as compared to the refinement_rule below.\<close>
theorem meta_refinement_rule:
  assumes "refines_hyper_program Cs1 Cs2"
      and "\<Turnstile> {P} [Cs2] {interp_assert Q}"
      and "no_exists_state Q"
    shows "\<Turnstile> {P} [Cs1] {interp_assert Q}"
proof (rule relational_hyper_hoare_tripleI)
  fix S
  assume "P S"
  with assms(2) have "interp_assert Q (sem_lifted Cs2 S)"
    by (simp add: relational_hyper_hoare_tripleE)
  with assms(1) assms(3) meta_refinement_rule_main show "interp_assert Q (sem_lifted Cs1 S)" by blast
qed



definition subs_cond where
 "subs_cond i j S = ((S i) \<subseteq> (S j))"


lemma refinement_rule_main:
  assumes "\<Turnstile> {subs_cond 0 1} [[0 \<mapsto> C1, 1 \<mapsto> C2]] {subs_cond 0 1}"
  shows "refines_hyper_program [0 \<mapsto> C1] [0 \<mapsto> C2]"
  unfolding refines_hyper_program_def
proof (intro allI ballI)
  fix Ss::"'a hyper_set"
  fix i
  let ?Ss' = "(\<lambda>i. if i = 0 then (Ss 0) else (if i = 1 then (Ss 0) else {}))" 
  have "(subs_cond 0 1) ?Ss'" unfolding subs_cond_def by auto
  with assms have "(subs_cond 0 1) (sem_lifted [0 \<mapsto> C1, 1 \<mapsto> C2] ?Ss')"
    by (simp add: relational_hyper_hoare_triple_def subs_cond_def)
  from this show "sem_lifted [0 \<mapsto> C1] Ss i \<subseteq> sem_lifted [0 \<mapsto> C2] Ss i" unfolding subs_cond_def 
    by(auto simp add:sem_lifted_def)
qed




text\<open>Rule inspired by the wp-refine rule of LHC but instead of meta-reasoning leverages RHHL's
      capability of directly deriving the refinement hyper-triple.\<close>
theorem refinement_rule:
  assumes "\<Turnstile> {subs_cond 0 1} [[0 \<mapsto> C1, 1 \<mapsto> C2]] {subs_cond 0 1}"
      and "\<Turnstile> {P} [[0 \<mapsto> C2]] {interp_assert Q}"
      and "no_exists_state Q"
    shows "\<Turnstile> {P} [[0 \<mapsto> C1]] {interp_assert Q}"
proof -
  from assms refinement_rule_main meta_refinement_rule show ?thesis by blast
qed


text\<open>Program statement which uses only syntactic program expressions and program boolean expressions.\<close>
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


fun pexp_var :: "'a pexp \<Rightarrow> nat list" where
"pexp_var (PVar v) = [v]" 
| "pexp_var (PConst _) = []"
| "pexp_var (PBinop pe1 _ pe2) = (pexp_var pe1) @ (pexp_var pe2)"
| "pexp_var (PFun _ pe) = pexp_var pe"


fun pbexp_var :: "'a pbexp \<Rightarrow> nat list" where
"pbexp_var (PBConst _) = []"
| "pbexp_var (PBAnd pb1 pb2) = (pbexp_var pb1) @ (pbexp_var pb2)"
| "pbexp_var (PBOr pb1 pb2) = (pbexp_var pb1) @ (pbexp_var pb2)"
| "pbexp_var (PBComp pe1 _ pe2) = (pexp_var pe1) @ (pexp_var pe2)"


text\<open>Gather all variables accessed by the program (read / written).\<close>
fun pvar :: "'a syn_stmt \<Rightarrow> nat list" where
"pvar (AssignS v pe) = v#(pexp_var pe)" |
"pvar (SeqS C1 C2) = (pvar C1) @ (pvar C2)" |
"pvar (IfS C1 C2) = (pvar C1) @ (pvar C2)" |
"pvar (SkipS) = []" |
"pvar (HavocS v) = [v]" |
"pvar (AssumeS pb) = pbexp_var pb" |
"pvar (WhileS C) = pvar C"



fun refinement_syn_assert_vars :: "nat list \<Rightarrow> 'a syn_assertion" where
"refinement_syn_assert_vars [] = (AConst True)" |
"refinement_syn_assert_vars (v#vs) = AAnd (AComp (EPVar 1 v) (=) (EPVar 0 v)) (refinement_syn_assert_vars vs)"

definition refinement_syn_assert :: "nat \<Rightarrow> nat \<Rightarrow> 'a syn_stmt \<Rightarrow> 'a syn_stmt \<Rightarrow> 'a syn_assertion" where
"refinement_syn_assert i j C1 C2 = (AForallState i (AExistsState j (refinement_syn_assert_vars ((pvar C1) @ (pvar C2)))))"

text\<open>Semantic version for the syntactic assertion above\<close>
definition refinement_assert where
"refinement_assert i j C1 C2 S = (\<forall>(li,\<sigma>i) \<in> (S i). (\<exists>(lj,\<sigma>j)\<in>(S j). (\<forall>x \<in> (set ((pvar C1) @ (pvar C2))). (\<sigma>i x) = (\<sigma>j x))))"


lemma refinement_syn_assert_vars_sound: "(\<forall>x \<in> (set Vs). ((snd \<sigma>) x) = ((snd \<sigma>') x)) = 
                                          sat_assertion [] [\<sigma>', \<sigma>] (refinement_syn_assert_vars Vs) S"
proof (induction Vs)
  case Nil
  then show ?case by(auto)
next
  case (Cons a Vs)
  then show ?case by(auto)
qed


lemma refinement_syn_assert_sound: "interp_assert (refinement_syn_assert i j C1 C2) S = (refinement_assert i j C1 C2) S"
  unfolding refinement_syn_assert_def refinement_assert_def
  apply(auto)
   apply (smt (verit, ccfv_threshold) case_prodI2 set_append snd_conv refinement_syn_assert_vars_sound)
  using refinement_syn_assert_vars_sound by fastforce


text\<open>Standard definition of the refinement relation between two programs\<close>
definition refines_program where
"refines_program C1 C2 = (\<forall>\<sigma> \<sigma>'. \<langle>C1, \<sigma>\<rangle> \<rightarrow> \<sigma>' \<longrightarrow> \<langle>C2, \<sigma>\<rangle> \<rightarrow> \<sigma>')"


lemma variable_preservation:
  assumes "\<langle>interp_syn_stmt C, \<sigma>\<rangle> \<rightarrow> \<sigma>'"
      and "x \<notin> (set (pvar C))" 
    shows "\<sigma> x = \<sigma>' x"
  using assms
proof (induction C arbitrary: \<sigma> \<sigma>')
  case (AssignS x1 x2)
  then show ?case by(auto)
next
  case (SeqS C1 C2)
  have "x \<notin> set (pvar (SeqS C1 C2)) \<Longrightarrow> x \<notin> set (pvar C1) \<and> x \<notin> set (pvar C2)" by auto
  with SeqS show ?case
    by (metis interp_syn_stmt.simps(2) single_sem_Seq_elim)
next
  case (IfS C1 C2)
  then show ?case by auto
next
  case SkipS
  then show ?case by auto
next
  case (HavocS x)
  then show ?case by auto
next
  case (AssumeS x)
  then show ?case by auto
next
  case (WhileS C)
  then show ?case by auto
qed

lemma refinement_hyper_triple_sound:
  assumes "\<Turnstile> {(refinement_assert 0 1 C1 C2)} [[0 \<mapsto> (interp_syn_stmt C1), 1 \<mapsto> (interp_syn_stmt C2)]] {(refinement_assert 0 1 C1 C2)}"
  shows "refines_program (interp_syn_stmt C1) (interp_syn_stmt C2)"
  unfolding refines_program_def
proof (intro allI impI)
  fix \<sigma> \<sigma>'
  assume asm: "\<langle>interp_syn_stmt C1, \<sigma>\<rangle> \<rightarrow> \<sigma>'"

  let ?S = "\<lambda>i. (if i = 0 then {(\<sigma>,\<sigma>)} else (if i = 1 then {(\<sigma>,\<sigma>)} else {}))"
  have "(refinement_assert 0 1 C1 C2) ?S" unfolding refinement_assert_def by(auto)
  with assms have H: "(refinement_assert 0 1 C1 C2) (sem_lifted [0 \<mapsto> (interp_syn_stmt C1), 1 \<mapsto> (interp_syn_stmt C2)] ?S)"
    using relational_hyper_hoare_tripleE by blast
  from variable_preservation have "\<And>\<phi> \<phi>'. (\<langle>interp_syn_stmt C1, \<sigma>\<rangle> \<rightarrow> \<phi>) \<and> (\<langle>interp_syn_stmt C2, \<sigma>\<rangle> \<rightarrow> \<phi>') \<and> (\<forall>x\<in>set (pvar C1) \<union> set (pvar C2). \<phi> x = \<phi>' x) \<Longrightarrow> \<phi> = \<phi>'"
    apply(auto)
  proof -
    fix \<phi> :: "nat \<Rightarrow> 'a" and \<phi>' :: "nat \<Rightarrow> 'a"
    assume a1: "\<forall>x\<in>set (pvar C1) \<union> set (pvar C2). \<phi> x = \<phi>' x"
    assume a2: "\<langle>interp_syn_stmt C2, \<sigma>\<rangle> \<rightarrow> \<phi>'"
    assume "\<langle>interp_syn_stmt C1, \<sigma>\<rangle> \<rightarrow> \<phi>"
    then have f3: "\<forall>n. \<phi> n = \<phi>' n \<or> \<sigma> n = \<phi> n"
      using a1 by (meson UnCI variable_preservation)
    have "\<forall>n. \<phi> n = \<phi>' n \<or> \<sigma> n = \<phi>' n"
      using a2 a1 by (meson UnCI variable_preservation)
    then show "\<phi> = \<phi>'"
      using f3 by fastforce
  qed
  with H asm show "\<langle>interp_syn_stmt C2, \<sigma>\<rangle> \<rightarrow> \<sigma>'" by(auto simp add:refinement_assert_def sem_lifted_def sem_def)
qed


lemma refines_program_lifted:
  assumes "refines_program C1 C2"
  shows "refines_hyper_program [0 \<mapsto> C1] [0 \<mapsto> C2]"
  unfolding refines_hyper_program_def 
proof (intro allI)
  fix S i 
  from assms show "sem_lifted [0 \<mapsto> C1] S i \<subseteq> sem_lifted [0 \<mapsto> C2] S i" unfolding refines_program_def
    apply(auto simp add:sem_lifted_def sem_def)
    by auto
qed

text\<open>Same as the refinement_rule but uses only syntactic hyper-assertions in the refinement hyper-triple.\<close>
theorem refinement_syn_rule:
  assumes "\<Turnstile> {interp_assert (refinement_syn_assert 0 1 C1 C2)} [[0 \<mapsto> (interp_syn_stmt C1), 1 \<mapsto> (interp_syn_stmt C2)]] {interp_assert (refinement_syn_assert 0 1 C1 C2)}"
      and "\<Turnstile> {P} [[0 \<mapsto> (interp_syn_stmt C2)]] {interp_assert Q}"
      and "no_exists_state Q"
    shows "\<Turnstile> {P} [[0 \<mapsto> (interp_syn_stmt C1)]] {interp_assert Q}"
proof -
  from refinement_syn_assert_sound refinement_hyper_triple_sound refines_program_lifted assms meta_refinement_rule show ?thesis
    by (smt (verit, ccfv_threshold) relational_hyper_hoare_tripleE relational_hyper_hoare_tripleI)
qed




text\<open>A symmetric rule to if_lockstep_arbitrary inspired by the right-to-left direction of LHC's wp-ifI\<close>
theorem if_lockstep_arbitrary_sym:
    assumes "\<forall>i\<in>I. entails P (\<lambda>S. ((holds_forall (bs i) (S i)))) \<or> entails P (\<lambda>S. ((holds_forall (lnot (bs i)) (S i))))"
        and "\<Turnstile> { P } [[ i \<mapsto> (if_then_else (bs i) (Cs1 i) (Cs2 i)) | i \<in> I ]] { Q }" 
      shows "\<Turnstile> { P } [[ i \<mapsto> (pick_branch P bs Cs1 Cs2 i) | i \<in> I]] { Q }"
proof -
  let ?bs' = "\<lambda>i. (if (entails P (\<lambda>S. (holds_forall (bs i) (S i)))) then (bs i) else (lnot_hyper bs i))"
  let ?Cs1' = "\<lambda>i. (if (entails P (\<lambda>S. (holds_forall (bs i) (S i)))) then (Cs1 i) else (Cs2 i))"
  let ?Cs2' = "\<lambda>i. (if (entails P (\<lambda>S. (holds_forall (bs i) (S i)))) then (Cs2 i) else (Cs1 i))"
  from assms if_equiv have equiv:"sem_equiv_hyper [ i \<mapsto> if_then_else (?bs' i) (?Cs1' i) (?Cs2' i) | i \<in> I ]
                         [ i \<mapsto> if_then_else (bs i) (Cs1 i) (Cs2 i) | i \<in> I ] P" by auto
  with assms(2) rewrite_rule have if_ht: "\<Turnstile> {P} [[ i \<mapsto> if_then_else (?bs' i) (?Cs1' i) (?Cs2' i) | i \<in> I ]] {Q}" by auto
  from assms(1) have hfa:"entails P (holds_forall_hyper I ?bs')"
    by(auto simp add:entails_def holds_forall_def holds_forall_hyper_def lnot_def lnot_hyper_def)
  hence ent_conj:"entails P (conj P (holds_forall_hyper I ?bs'))"
    by (metis (lifting) entail_conj entails_def)
  with if_ht have "\<Turnstile> {conj P (holds_forall_hyper I ?bs')} [[ i \<mapsto> if_then_else (?bs' i) (?Cs1' i) (?Cs2' i) | i \<in> I ]] {Q}"
    using entail_conj_weaken precondition_conseq by blast
  with if_lockstep_true_sym have "\<Turnstile> { conj P (holds_forall_hyper I ?bs') } [[i \<mapsto> (?Cs1' i) | i \<in> I]] { Q }"
    by fastforce
  with ent_conj precondition_conseq have "\<Turnstile> { P } [[i \<mapsto> (?Cs1' i) | i \<in> I]] { Q }" 
    by auto
  thus ?thesis by auto
qed


subsection \<open>Structural Rules\<close>
text\<open>From the LHC's structural rules we actually only adopt the reindexing rule, as other rules 
    are not concerned with relational reasoning\<close>


lemma reindex_inv_org:
  assumes "bij \<pi>"
  shows "reindex_hyper_stuff \<pi> (reindex_hyper_stuff (inv \<pi>) S) = S"
  unfolding reindex_hyper_stuff_def
  by (metis (no_types, lifting) ext assms bij_betw_def inv_f_f)

text\<open>A classical reindexing rule for a bijective reindexing which generelizes LHC's wp-idx and idx rules\<close>
theorem reindex_rule:
  assumes "\<Turnstile> {P} [Cs] {Q}"
      and "bij \<pi>"
    shows "\<Turnstile> {reindex_assertion \<pi> P} [reindex_hyper_stuff (inv \<pi>) Cs] {reindex_assertion \<pi> Q}"
proof (rule relational_hyper_hoare_tripleI)
  fix S
  assume "reindex_assertion \<pi> P S"
  hence "P (reindex_hyper_stuff \<pi> S)" unfolding reindex_assertion_def by auto
  with assms(1) have "Q (sem_lifted Cs (reindex_hyper_stuff \<pi> S))" unfolding relational_hyper_hoare_triple_def
    by auto
  with sem_lifted_reindex reindex_inv_org \<open>bij \<pi>\<close> have "Q (reindex_hyper_stuff \<pi> (sem_lifted (reindex_hyper_stuff (inv \<pi>) Cs) S))"
    by metis
  then show "reindex_assertion \<pi> Q (sem_lifted (reindex_hyper_stuff (inv \<pi>) Cs) S)" unfolding reindex_assertion_def by auto
qed



lemma syn_reindexing_soundness: "reindex_assertion \<pi> (interp_assert Q) = interp_assert (reindex_syn_assertion \<pi> Q)"
proof (induction Q)
  case (AConst x)
  then show ?case 
    by (simp add: reindex_assertion_def)
next
  case (AComp x1a x2 x3)
  then show ?case 
    by (simp add: reindex_assertion_def)
next
  case (AForallState x1a Q)
  then show ?case 
    by (metis reindex_assertion_def reindex_both_impl(1,2))
next
  case (AExistsState x1a Q)
  then show ?case 
    by (metis reindex_assertion_def reindex_both_impl(1,2))
next
  case (AForall Q)
  then show ?case 
    by (metis reindex_assertion_def reindex_both_impl(1,2))
next
  case (AExists Q)
  then show ?case 
    by (metis reindex_assertion_def reindex_both_impl(1,2))
next
  case (AOr Q1 Q2)
  then show ?case 
    by (metis reindex_assertion_def reindex_both_impl(1,2))
next
  case (AAnd Q1 Q2)
  then show ?case 
    by (metis reindex_assertion_def reindex_both_impl(1,2))
qed


lemma reindexing_preserves_no_exist_state:
  assumes "no_exists_state Q"
  shows "no_exists_state (reindex_syn_assertion \<pi> Q)"
  using assms
  apply (induction Q)
  apply(simp_all)
  done




section \<open>Other useful rules\<close>


abbreviation assume_hyper_set where
"assume_hyper_set I Bs S \<equiv> (\<lambda>i. (if i \<in> I then { (l, \<sigma>) |l \<sigma>. (l, \<sigma>) \<in> (S i) \<and> (Bs i) \<sigma>} else S i))"

abbreviation assume_prec where
"assume_prec P I Bs S \<equiv> P (assume_hyper_set I Bs S)"

theorem assume_lockstep:
  shows "\<Turnstile>  { assume_prec P I Bs} [[i \<mapsto> Assume (Bs i) |i \<in> I]] {P}"
proof (rule relational_hyper_hoare_tripleI)
  fix S
  assume asm: "assume_prec P I Bs S"
  have "(assume_hyper_set I Bs S) = (sem_lifted [i \<mapsto> Assume (Bs i) |i \<in> I] S)"
  proof
    fix i
    show "(assume_hyper_set I Bs S) i = (sem_lifted [i \<mapsto> Assume (Bs i) |i \<in> I] S) i"
      by(auto simp add:sem_lifted_def map_comprehension_def sem_def intro:SemAssume)
  qed
  with asm show "P (sem_lifted [i \<mapsto> Assume (Bs i) |i \<in> I] S)" by auto
qed


theorem false_prec:
  shows "\<Turnstile> {(\<lambda>S. False)} [Cs] {Q}"
proof (intro relational_hyper_hoare_tripleI)
  fix S
  assume "False"
  thus "Q (sem_lifted Cs S)" by auto
qed


theorem skip_lockstep:
  shows "\<Turnstile> {P} [[i \<mapsto> Skip |i \<in> I]] {P}"
proof (rule relational_hyper_hoare_tripleI)
  fix S
  assume "P S"
  have eq:"(sem_lifted (map_comprehension (\<lambda>i. Skip) (\<lambda>i. i \<in> I)) S) = S"
    apply(rule) using SemSkip
    by(auto simp add:sem_lifted_def map_comprehension_def sem_def)
  show "P (sem_lifted (map_comprehension (\<lambda>i. Skip) (\<lambda>i. i \<in> I)) S)"
    apply(simp only:eq) using \<open>P S\<close> by auto
qed



theorem postcondition_conj:
  assumes "\<Turnstile> {P} [Cs] {Q1}"
      and "\<Turnstile> {P} [Cs] {Q2}"
    shows "\<Turnstile> {P} [Cs] {conj Q1 Q2}"
proof (intro relational_hyper_hoare_tripleI)
  fix S
  assume "P S"
  from \<open>P S\<close> assms(1) have H1:"Q1 (sem_lifted Cs S)"
    by (simp add: relational_hyper_hoare_tripleE)
  from \<open>P S\<close> assms(2) have H2:"Q2 (sem_lifted Cs S)"
    by (simp add: relational_hyper_hoare_tripleE)
  show "conj Q1 Q2 (sem_lifted Cs S)"
    by(auto simp add:conj_def H1 H2)
qed

theorem if_lockstep_trueG:
  assumes "\<Turnstile> { conj P (holds_forall_hyper I bs) } [Cs' ++ [i \<mapsto> (Cs1 i) | i \<in> I]] { Q }"
      and "dom Cs' \<inter> I = {}"
  shows "\<Turnstile> { conj P (holds_forall_hyper I bs)} [Cs' ++ [ i \<mapsto> (if_then_else (bs i) (Cs1 i) (Cs2 i)) | i \<in> I ]] { Q }"
proof -
  from assms have dcs1:"dom Cs' \<inter> (dom [i \<mapsto> (Cs1 i) | i \<in> I]) = {}" 
    by(auto simp add:map_comprehension_def dom_def)
  from dcs1 assms split_rule have H11:"\<Turnstile> { conj P (holds_forall_hyper I bs) } [Cs'] { wp_RHHL [i \<mapsto> (Cs1 i) | i \<in> I] Q}"
    by blast
  have H10:"\<Turnstile> { conj P (holds_forall_hyper I bs) } [Cs'] { (holds_forall_hyper I bs) }" 
    apply(intro relational_hyper_hoare_tripleI)
    using assms(2)
    apply(auto simp add:sem_lifted_def conj_def holds_forall_hyper_def dom_def map_comprehension_def)
    by (metis (mono_tags, lifting) IntI assms(2) domIff empty_iff map_comprehension_def option.discI partial_sem.simps(2)
        snd_eqD)
  have H: "\<Turnstile> { conj P (holds_forall_hyper I bs) } [Cs'] { conj (wp_RHHL [i \<mapsto> (Cs1 i) | i \<in> I] Q) (holds_forall_hyper I bs) }" 
    apply(rule postcondition_conj)
    by(auto simp add:H11 H10)
  from dcs1 assms split_rule have H20:"\<Turnstile> { wp_RHHL [i \<mapsto> (Cs1 i) | i \<in> I] Q} [[i \<mapsto> (Cs1 i) | i \<in> I]] { Q }"
    by blast
  have  H2: "\<Turnstile> { conj (wp_RHHL [i \<mapsto> (Cs1 i) | i \<in> I] Q) (holds_forall_hyper I bs)} [[i \<mapsto> (Cs1 i) | i \<in> I]] { Q }" 
    apply(rule precondition_conseq[where ?P'="(wp_RHHL [i \<mapsto> (Cs1 i) | i \<in> I] Q)"])
    prefer 2
    apply(simp only:H20)
    apply(intro entailsI)
    by(auto simp add:conj_def)
  show ?thesis
    apply(rule rel_extension[where ?R="conj (wp_RHHL [i \<mapsto> (Cs1 i) | i \<in> I] Q) (holds_forall_hyper I bs)"])
      apply(simp only:H)
     apply(rule if_lockstep_true)
     apply(simp only:H2)
    using assms(2)
    by(auto simp add:dom_def map_comprehension_def)
qed


theorem if_lockstep_falseG:
  assumes "\<Turnstile> { conj P (holds_forall_hyper I (lnot_hyper bs)) } [Cs' ++ [i \<mapsto> (Cs2 i) | i \<in> I]] { Q }"
      and "dom Cs' \<inter> I = {}"
  shows "\<Turnstile> { conj P (holds_forall_hyper I (lnot_hyper bs))} [Cs' ++ [ i \<mapsto> (if_then_else (bs i) (Cs1 i) (Cs2 i)) | i \<in> I ]] { Q }"
proof -
  from assms have dcs2:"dom Cs' \<inter> (dom [i \<mapsto> (Cs2 i) | i \<in> I]) = {}" 
    by(auto simp add:map_comprehension_def dom_def)
  from assms(1) dcs2 split_rule have H11:"\<Turnstile> { conj P (holds_forall_hyper I (lnot_hyper bs)) } [Cs'] { wp_RHHL [i \<mapsto> (Cs2 i) | i \<in> I] Q}"
    by blast
  have H10:"\<Turnstile> { conj P (holds_forall_hyper I (lnot_hyper bs)) } [Cs'] { (holds_forall_hyper I (lnot_hyper bs)) }" 
    apply(intro relational_hyper_hoare_tripleI)
    using assms(2)
    apply(auto simp add:sem_lifted_def conj_def holds_forall_hyper_def dom_def map_comprehension_def)
    by (metis (mono_tags, lifting) IntI assms(2) domIff empty_iff map_comprehension_def option.discI partial_sem.simps(2)
        snd_eqD)
  have H: "\<Turnstile> { conj P (holds_forall_hyper I (lnot_hyper bs)) } [Cs'] { conj (wp_RHHL [i \<mapsto> (Cs2 i) | i \<in> I] Q) (holds_forall_hyper I (lnot_hyper bs)) }" 
    apply(rule postcondition_conj)
    by(auto simp add:H11 H10)
  from dcs2 assms split_rule have H20:"\<Turnstile> { wp_RHHL [i \<mapsto> (Cs2 i) | i \<in> I] Q} [[i \<mapsto> (Cs2 i) | i \<in> I]] { Q }"
    by blast
  have  H2: "\<Turnstile> { conj (wp_RHHL [i \<mapsto> (Cs2 i) | i \<in> I] Q) (holds_forall_hyper I (lnot_hyper bs))} [[i \<mapsto> (Cs2 i) | i \<in> I]] { Q }" 
    apply(rule precondition_conseq[where ?P'="(wp_RHHL [i \<mapsto> (Cs2 i) | i \<in> I] Q)"])
    prefer 2
    apply(simp only:H20)
    apply(intro entailsI)
    by(auto simp add:conj_def)
  show ?thesis
    apply(rule rel_extension[where ?R="conj (wp_RHHL [i \<mapsto> (Cs2 i) | i \<in> I] Q) (holds_forall_hyper I (lnot_hyper bs))"])
      apply(simp only:H)
     apply(rule if_lockstep_false)
     apply(simp add:H2)
    using assms(2)
    by(auto simp add:dom_def map_comprehension_def)
qed


theorem if_lockstepG:
  assumes "\<Turnstile> { conj P (holds_forall_hyper I bs) } [Cs' ++ [i \<mapsto> (Cs1 i) | i \<in> I]] { Q }"
    and   "\<Turnstile> { conj P (holds_forall_hyper I (lnot_hyper bs)) } [Cs' ++ [i \<mapsto> (Cs2 i) | i \<in> I]] { Q }"
      and "dom Cs' \<inter> I = {}"
    shows "\<Turnstile> { conj P (low_exp_hyper I bs)} [Cs' ++ [ i \<mapsto> (if_then_else (bs i) (Cs1 i) (Cs2 i)) | i \<in> I ]] { Q }"
proof -
  from if_lockstep_trueG assms(1) assms(3) have "\<Turnstile> { conj P (holds_forall_hyper I bs)} [Cs' ++ [ i \<mapsto> (if_then_else (bs i) (Cs1 i) (Cs2 i)) | i \<in> I ]] { Q }"
    by (simp add: if_lockstep_trueG)
  moreover from if_lockstep_false assms(2) assms(3) have "\<Turnstile> { conj P (holds_forall_hyper I (lnot_hyper bs))} [Cs' ++ [ i \<mapsto> (if_then_else (bs i) (Cs1 i) (Cs2 i)) | i \<in> I ]] { Q }"
    by (simp add: if_lockstep_falseG)
  ultimately show ?thesis 
    unfolding relational_hyper_hoare_triple_def
  proof (intro ballI allI impI)
    fix S
    assume asm1:"\<forall>S. Logic.conj P (holds_forall_hyper I bs) S \<longrightarrow>
              Q (sem_lifted (Cs' ++ map_comprehension (\<lambda>i. if_then_else (bs i) (Cs1 i) (Cs2 i)) (\<lambda>i. i \<in> I)) S)" and
          asm2:"\<forall>S. Logic.conj P (holds_forall_hyper I (lnot_hyper bs)) S \<longrightarrow>
              Q (sem_lifted (Cs' ++ map_comprehension (\<lambda>i. if_then_else (bs i) (Cs1 i) (Cs2 i)) (\<lambda>i. i \<in> I)) S)" and
          asm3:"Logic.conj P (low_exp_hyper I bs) S"
    hence "conj P (holds_forall_hyper I bs) S \<or> conj P (holds_forall_hyper I (lnot_hyper bs)) S" using low_exp_either conj_def by metis
    thus "Q (sem_lifted (Cs' ++ map_comprehension (\<lambda>i. if_then_else (bs i) (Cs1 i) (Cs2 i)) (\<lambda>i. i \<in> I)) S)"
    proof
      assume "Logic.conj P (holds_forall_hyper I bs) S"
      with asm1 show ?thesis by auto
    next 
      assume "Logic.conj P (holds_forall_hyper I (lnot_hyper bs)) S"
      with asm2 show ?thesis by auto
    qed
  qed
qed


lemma sem_equiv_hyper_extend:
  assumes "sem_equiv_hyper Cs1 Cs2 P"
      and "dom Cs' \<inter> dom Cs1 = {}"
      and "dom Cs' \<inter> dom Cs2 = {}"
    shows "sem_equiv_hyper (Cs' ++ Cs1) (Cs' ++ Cs2 )P"
proof(auto simp add:sem_equiv_hyper_def)
  fix S
  assume "P S"
  show "sem_lifted (Cs' ++ Cs1) S = sem_lifted (Cs' ++ Cs2) S "
    apply(rule)
    using assms
    apply(auto simp add:sem_lifted_def map_add_def sem_equiv_hyper_def dom_def)
     apply (metis \<open>P S\<close> assms(2,3) inf_commute map_add_comm map_add_def sem_lifted_def sem_lifted_on_disjoint_maps_seq)
    by (metis \<open>P S\<close> assms(2,3) inf_commute map_add_comm map_add_def sem_lifted_def sem_lifted_on_disjoint_maps_seq)
qed

theorem if_lockstep_arbitraryG:
    assumes "\<forall>i\<in>I. entails P (\<lambda>S. ((holds_forall (bs i) (S i)))) \<or> entails P (\<lambda>S. ((holds_forall (lnot (bs i)) (S i))))"
    and     "\<Turnstile> { P } [Cs' ++ [ i \<mapsto> (pick_branch P bs Cs1 Cs2 i) | i \<in> I]] { Q }"
    and     "dom Cs' \<inter> I = {}"
  shows     "\<Turnstile> { P } [Cs' ++ [ i \<mapsto> (if_then_else (bs i) (Cs1 i) (Cs2 i)) | i \<in> I ]] { Q }"
proof -
  let ?bs' = "\<lambda>i. (if (entails P (\<lambda>S. (holds_forall (bs i) (S i)))) then (bs i) else (lnot_hyper bs i))"
  let ?Cs1' = "\<lambda>i. (if (entails P (\<lambda>S. (holds_forall (bs i) (S i)))) then (Cs1 i) else (Cs2 i))"
  let ?Cs2' = "\<lambda>i. (if (entails P (\<lambda>S. (holds_forall (bs i) (S i)))) then (Cs2 i) else (Cs1 i))"
  from assms have dif1:"dom Cs' \<inter> (dom [ i \<mapsto> if_then_else (bs i) (Cs1 i) (Cs2 i) | i \<in> I ]) = {}" 
    by(auto simp add:map_comprehension_def dom_def)
  from assms have dif2:"dom Cs' \<inter> (dom [ i \<mapsto> if_then_else (?bs' i) (?Cs1' i) (?Cs2' i) | i \<in> I ]) = {}" 
    by(auto simp add:map_comprehension_def dom_def)
  from assms if_equiv have equiv:"sem_equiv_hyper [ i \<mapsto> if_then_else (?bs' i) (?Cs1' i) (?Cs2' i) | i \<in> I ]
                         [ i \<mapsto> if_then_else (bs i) (Cs1 i) (Cs2 i) | i \<in> I ] P" by auto
  with sem_equiv_hyper_extend dif1 dif2 have equiv:"sem_equiv_hyper( Cs' ++ [ i \<mapsto> if_then_else (?bs' i) (?Cs1' i) (?Cs2' i) | i \<in> I ])
                         (Cs' ++ [ i \<mapsto> if_then_else (bs i) (Cs1 i) (Cs2 i) | i \<in> I ]) P" by auto
  from assms(1) have hfa:"entails P (holds_forall_hyper I ?bs')"
    by(auto simp add:entails_def holds_forall_def holds_forall_hyper_def lnot_def lnot_hyper_def)
  hence ent_conj:"entails P (conj P (holds_forall_hyper I ?bs'))"
    by (metis (lifting) entail_conj entails_def)
  have "\<Turnstile> {conj P (holds_forall_hyper I ?bs')} [Cs' ++ [ i \<mapsto> if_then_else (?bs' i) (?Cs1' i) (?Cs2' i) | i \<in> I ]] {Q}" 
  proof(rule if_lockstep_trueG)
    show "\<Turnstile> {Logic.conj P
         (holds_forall_hyper I (pick_branch P bs bs (lnot_hyper bs)))} [Cs'++map_comprehension (pick_branch P bs Cs1 Cs2) (\<lambda>i. i \<in> I)] {Q}"
      unfolding relational_hyper_hoare_triple_def
    proof(intro allI impI)
      fix S
      assume "Logic.conj P (holds_forall_hyper I (pick_branch P bs bs (lnot_hyper bs))) S"
      hence "P S"
        by (simp add: conj_def)
      with assms(2) show "Q (sem_lifted (Cs'++(map_comprehension (pick_branch P bs Cs1 Cs2) (\<lambda>i. i \<in> I))) S)"
        by (simp add: relational_hyper_hoare_triple_def) 
    qed
  next 
    show "dom Cs' \<inter> I = {}" using assms by auto
  qed
  with ent_conj precondition_conseq have "\<Turnstile> {P} [Cs' ++ [ i \<mapsto> if_then_else (?bs' i) (?Cs1' i) (?Cs2' i) | i \<in> I ]] {Q}" by auto
  with equiv rewrite_rule show ?thesis by auto
qed

section \<open>Mini case study\<close>


definition if_then_else_skip where
"if_then_else_skip b C = if_then_else b C Skip "


notation if_then_else  ("IF _ THEN _ ELSE _" [0, 0, 61] 61)
notation if_then_else_skip  ("IF _  THEN _ FI" [0, 60] 61)
notation while_cond  ("WHILE _ DO _" [0, 61] 61)


abbreviation four_to_hundred :: "nat \<Rightarrow> nat \<Rightarrow> (nat, nat) stmt" where
"four_to_hundred i x \<equiv>  
  i ::= (\<lambda>s. 100);;
  x ::= (\<lambda>s. 1);;
  WHILE (\<lambda>s. (s i) > 0) DO (
     x ::= (\<lambda>s. 4*(s x));;
     i ::= (\<lambda>s. (s i) - 1)
    )
"


abbreviation four_to_hundred_prime :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat, nat) stmt" where
"four_to_hundred_prime i x c \<equiv>  
  i ::= (\<lambda>s. 100);;
  x ::= (\<lambda>s. 1);;
  c ::= (\<lambda>s. 0);;
  WHILE (\<lambda>s. (s i) > 0) DO (
     IF (\<lambda>s. prime (s c)) THEN (
       x ::= (\<lambda>s. 4*(s x));;
       i ::= (\<lambda>s. (s i) - 1)
     ) FI;;
    c ::= (\<lambda>s. (s c) + 1)
  )
"


lemma entails_conj:
   assumes "entails P Q1"
    and "entails P Q2"
  shows "entails P (conj Q1 Q2)"
  using assms 
  apply(intro entailsI)
  by(auto simp add:entails_def conj_def)

proposition
  fixes i::nat and x::nat and c::nat
  assumes "i \<noteq> x \<and> x \<noteq> c \<and> i \<noteq> c"
  shows "(\<Turnstile>  {(\<lambda>S::nat hyper_set. \<forall>\<sigma>0 \<in> (S 0). \<exists>\<sigma>1 \<in> (S 1). (snd \<sigma>0 x) = (snd \<sigma>1 x))} 
            [[0 \<mapsto> four_to_hundred i x, 1 \<mapsto> four_to_hundred_prime i x c]::nat hyper_program] 
             {(\<lambda>S::nat hyper_set. \<forall>\<sigma>0 \<in> (S 0). \<exists>\<sigma>1 \<in> (S 1). (snd \<sigma>0 x) = (snd \<sigma>1 x))})"
proof -
  let ?Cs = "[0 \<mapsto> four_to_hundred i x, 1 \<mapsto> four_to_hundred_prime i x c]::nat hyper_program"
  let ?Cs1 = "[0 \<mapsto> i ::= (\<lambda>s. 100), 1 \<mapsto> i ::= (\<lambda>s. 100)]::nat hyper_program"
  let ?Cs2 = "[0 \<mapsto> x ::= (\<lambda>s. 1), 1 \<mapsto> x ::= (\<lambda>s. 1)]::nat hyper_program"
  let ?Cs3 = "[ 0 \<mapsto> WHILE (\<lambda>s. (s i) > 0) DO (
                         x ::= (\<lambda>s. 4*(s x));;
                         i ::= (\<lambda>s. (s i) - 1)
                     ),
                1 \<mapsto>  c ::= (\<lambda>s. 0);;
                      WHILE (\<lambda>s. (s i) > 0) DO (
                         IF (\<lambda>s. prime (s c)) THEN (
                           x ::= (\<lambda>s. 4*(s x));;
                           i ::= (\<lambda>s. (s i) - 1)
                         ) FI;;
                        c ::= (\<lambda>s. (s c) + 1)
                      )]::nat hyper_program"
  let ?Loops = "[ 0 \<mapsto> WHILE (\<lambda>s. (s i) > 0) DO (
                         x ::= (\<lambda>s. 4*(s x));;
                         i ::= (\<lambda>s. (s i) - 1)
                     ),
                1 \<mapsto>  WHILE (\<lambda>s. (s i) > 0) DO (
                         IF (\<lambda>s. prime (s c)) THEN (
                           x ::= (\<lambda>s. 4*(s x));;
                           i ::= (\<lambda>s. (s i) - 1)
                         ) FI;;
                        c ::= (\<lambda>s. (s c) + 1)
                      )]::nat hyper_program"
  let ?Loop2 = "(WHILE (\<lambda>s. (s i) > 0) DO (
                         IF (\<lambda>s. prime (s c)) THEN (
                           x ::= (\<lambda>s. 4*(s x));;
                           i ::= (\<lambda>s. (s i) - 1)
                         ) FI;;
                        c ::= (\<lambda>s. (s c) + 1)
                      ))::(nat, nat) stmt"
  let ?conds = "\<lambda>j::nat. (\<lambda>s::(nat, nat) pstate. (s i) > 0)"
  let ?bodies = "\<lambda>j::nat. if j = 0 then    x ::= (\<lambda>s::(nat, nat) pstate. 4*(s x));;
                                      i ::= (\<lambda>s. (s i) - 1) 
                      else            IF (\<lambda>s. prime (s c)) THEN (
                                        x ::= (\<lambda>s. 4*(s x));;
                                        i ::= (\<lambda>s. (s i) - 1)
                                      ) FI;;
                                      c ::= (\<lambda>s. (s c) + 1)"
  let ?C1.1 = "[1 \<mapsto> IF (\<lambda>s. prime (s c)) THEN (
                                        x ::= (\<lambda>s. 4*(s x));;
                                        i ::= (\<lambda>s. (s i) - 1)
                                      ) FI]::nat hyper_program"
  let ?C1.2 = "[1 \<mapsto> c ::= (\<lambda>s. (s c) + 1)]::nat hyper_program"
  let ?LBs.1 = "[0 \<mapsto> x ::= (\<lambda>s::(nat, nat) pstate. 4*(s x));; i ::= (\<lambda>s. (s i) - 1),
                 1 \<mapsto> IF (\<lambda>s. prime (s c)) THEN (
                                        x ::= (\<lambda>s. 4*(s x));;
                                        i ::= (\<lambda>s. (s i) - 1)
                                      ) FI]::nat hyper_program"
  let ?LBs.2 = "[1 \<mapsto> c ::= (\<lambda>s. (s c) + 1)]::nat hyper_program"
  let ?LBs1p1 = "[0 \<mapsto> x ::= (\<lambda>s::(nat, nat) pstate. 4*(s x)),
                   1 \<mapsto> x ::= (\<lambda>s::(nat, nat) pstate. 4*(s x))]::nat hyper_program"
  let ?LBs1p2 = "[0 \<mapsto> i ::= (\<lambda>s. (s i) - 1),
                   1 \<mapsto> i ::= (\<lambda>s. (s i) - 1)]::nat hyper_program"
  let ?Iv_p1 = "(\<lambda>S::nat hyper_set. (\<forall>(l0,\<sigma>0) \<in> (S 0). \<exists>(l1,\<sigma>1) \<in> (S 1). (\<sigma>0 x) = (\<sigma>1 x) \<and> (\<sigma>0 i) = (\<sigma>1 i))
                                          \<and>
                (\<forall>\<sigma>0 \<in> (S 0). \<forall>\<sigma>1 \<in> (S 1). (snd \<sigma>0 i) = (snd \<sigma>1 i))
                                          \<and>
                 (\<forall>\<sigma>0 \<in> (S 0). \<forall>\<sigma>0' \<in> (S 0). (snd \<sigma>0 i) = (snd \<sigma>0' i))
                                          \<and>
                 (\<forall>\<sigma>1 \<in> (S 1). \<forall>\<sigma>1' \<in> (S 1). (snd \<sigma>1 i) = (snd \<sigma>1' i)))"
  let ?Iv = "(\<lambda>n::nat. (\<lambda>S::nat hyper_set. (\<forall>\<sigma>0 \<in> (S 0). \<exists>\<sigma>1 \<in> (S 1). (snd \<sigma>0 x) = (snd \<sigma>1 x) \<and> (snd \<sigma>0 i) = (snd \<sigma>1 i))
                                          \<and>
                (\<forall>\<sigma>0 \<in> (S 0). \<forall>\<sigma>1 \<in> (S 1). (snd \<sigma>0 i) = (snd \<sigma>1 i))
                                          \<and>
                 (\<forall>\<sigma>0 \<in> (S 0). \<forall>\<sigma>0' \<in> (S 0). (snd \<sigma>0 i) = (snd \<sigma>0' i))
                                          \<and>
                 (\<forall>\<sigma>1 \<in> (S 1). \<forall>\<sigma>1' \<in> (S 1). (snd \<sigma>1 i) = (snd \<sigma>1' i))
                                          \<and>
                          (\<forall>\<sigma>1 \<in> (S 1). (snd \<sigma>1 c) = n)))"
  have eq0: "?Cs = hyper_seq ?Cs1 (hyper_seq ?Cs2 ?Cs3)" apply(rule) unfolding hyper_seq_def
    by(auto)
  (*Step 1*)
  show ?thesis
    apply(simp only:eq0)
  proof(rule lockstep_seq[where ?R = "?Iv_p1"])
    have eq1: "[0 \<mapsto> i ::= (\<lambda>s. 100), 1 \<mapsto> i ::= (\<lambda>s. 100)] = [j \<mapsto> (\<lambda>j. i ::= (\<lambda>s. 100)) j | j \<in> {0,1}]"
      apply(rule)
      by(auto simp add:map_comprehension_def)
    show "\<Turnstile> {(\<lambda>S::nat hyper_set. \<forall>\<sigma>0 \<in> (S 0). \<exists>\<sigma>1 \<in> (S 1). (snd \<sigma>0 x) = (snd \<sigma>1 x))} 
                  [[0 \<mapsto> i ::= (\<lambda>s. 100),1 \<mapsto> i ::= (\<lambda>s. 100)]] 
             {?Iv_p1}"
    apply(simp only:eq1)
    apply(rule precondition_conseq)
    prefer 2
    apply(rule assign_lockstep)
    using assms
    apply(auto simp add: entails_def)
    by fastforce
  next
    (*Step 2*)
    show "\<Turnstile> {?Iv_p1} 
                            [(hyper_seq ?Cs2 ?Cs3)::nat hyper_program] 
                {(\<lambda>S::nat hyper_set. \<forall>\<sigma>0 \<in> (S 0). \<exists>\<sigma>1 \<in> (S 1). (snd \<sigma>0 x) = (snd \<sigma>1 x))}"
    proof (rule lockstep_seq[where ?R = "?Iv_p1"])
      have eq2: "[0 \<mapsto> x ::= (\<lambda>s. 1), 1 \<mapsto> x ::= (\<lambda>s. 1)] = [j \<mapsto> (\<lambda>j. x ::= (\<lambda>s. 1)) j | j \<in> {0,1}]"
        apply(rule)
        by(auto simp add:map_comprehension_def)
      show "\<Turnstile> {?Iv_p1} 
                    [[0 \<mapsto> x ::= (\<lambda>s. 1), 1 \<mapsto> x ::= (\<lambda>s. 1)]] 
               {?Iv_p1}"
      apply(simp only:eq2)
      apply(rule precondition_conseq)
      prefer 2
      apply(rule assign_lockstep)
        using assms
        unfolding entails_def
        apply(intro allI impI conjI)
           apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(2) by(fastforce) qed
          apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(5) by(fastforce) qed
         apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(6) by(fastforce) qed
        apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(7) by(fastforce) qed
        done
    next 
      (*Step 3*)
      show "\<Turnstile> {?Iv_p1} 
                                         [?Cs3::nat hyper_program] 
                  {(\<lambda>S::nat hyper_set. \<forall>\<sigma>0 \<in> (S 0). \<exists>\<sigma>1 \<in> (S 1). (snd \<sigma>0 x) = (snd \<sigma>1 x))}"
        apply(rule progress_any[where ?i="1" and ?R = "?Iv 0"])
    
        apply(simp del: add_Suc_right One_nat_def)
      proof -
        have eq3: "[1 \<mapsto> c ::= (\<lambda>s. 0)] = [j \<mapsto> (\<lambda>j. c ::= (\<lambda>s. 0)) j | j \<in>{1}]"
          apply(rule)
          by(auto simp add:map_comprehension_def)
        show "\<Turnstile> {?Iv_p1} [[1 \<mapsto> c ::= (\<lambda>s. 0)]] {?Iv 0}"
          apply(simp only:eq3)
          apply(rule precondition_conseq)
           prefer 2
           apply(rule assign_lockstep)
          using assms
        unfolding entails_def
        apply(intro allI impI conjI)
           apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(2) assms(1) by(fastforce) qed
          apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(5) assms(1) by(fastforce) qed
         apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(6) assms(1) by(fastforce) qed
        apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(7) assms(1) by(fastforce) qed
        apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(7) assms(1) by(fastforce) qed
        done
      next
        have eq4: "?Cs3(1 \<mapsto> ?Loop2) = ?Loops"
          apply(rule)
          by(auto simp add:map_comprehension_def)
        have eq5: "?Loops = [j \<mapsto> while_cond (?conds j) (?bodies j) | j \<in> {0::nat,1::nat}]" 
          apply(rule)
          by(auto simp add:map_comprehension_def)
        (*Step 4*)
        let ?Q = "\<lambda>S::nat hyper_set. \<forall>\<sigma>0\<in>S 0. \<exists>\<sigma>1\<in>S 1. (snd \<sigma>0 x) = (snd \<sigma>1 x)"
        let ?V = "\<lambda>J::nat set. if J = {0,1} then (\<lambda>S::nat hyper_set. (\<forall>(\<sigma>1)\<in>(S 1). prime ((snd \<sigma>1) c))) else (
                      if J = {1} then (\<lambda>S::nat hyper_set. (\<forall>\<sigma>1\<in>(S 1). \<not>prime ((snd \<sigma>1) c))) else (\<lambda>S::nat hyper_set. False))"
        show "\<Turnstile> {?Iv 0} [?Cs3(1 \<mapsto> ?Loop2)] {?Q}"
          apply(simp only:eq4)
          apply(simp only:eq5)
          apply(rule postcondition_conseq[where Q' = "conj ?Q (holds_forall_hyper {0,1} (lnot_hyper ?conds))"])
           apply (simp add: entail_conj_weaken)
          apply(rule while_nonfixed_alignment5[where V = "?V" and Q = "(\<lambda>n. ?Q)" and ?Q_inf="?Q"  and I="{0,1}" and ?bs = ?conds and ?Cs = ?bodies and Iv="?Iv"])
        proof -
          (*Step 4.1*)
          show "\<forall>n. \<forall>J\<in>(Pow {0,1} - {{}}). \<Turnstile> { conj (?Iv n) (conj (holds_for_prog_set J ?conds) (?V J))} [[i \<mapsto> ?bodies i | i \<in> J]] { ?Iv (Suc n) }"
          proof (intro allI ballI)
            fix n 
            fix J ::"nat set"
            assume "J\<in>(Pow {0,1} - {{}})"
            hence "J = {0} \<or> J = {1} \<or> J = {0,1}" by auto
            thus " \<Turnstile> { conj (?Iv n) (conj (holds_for_prog_set J ?conds) (?V J))} [[i \<mapsto> ?bodies i | i \<in> J]] { ?Iv (Suc n) }"
            proof (elim disjE)
              assume "J = {0}"
              (*Step 4.1.1*)
              show "\<Turnstile> { conj (?Iv n) (conj (holds_for_prog_set J ?conds) (?V J))} [[i \<mapsto> ?bodies i | i \<in> J]] { ?Iv (Suc n) }"
                apply(rule precondition_conseq[where ?P'="\<lambda>S. False"])
                 prefer 2
                 apply(rule false_prec)
                apply(intro entailsI)
                unfolding conj_def
                using \<open>J = {0}\<close>
                by(auto)
            next
              assume "J = {1}"
              have eq:"[i \<mapsto> ?bodies i | i \<in> J] = hyper_seq ?C1.1 ?C1.2"
                apply(rule) using \<open>J = {1}\<close> unfolding hyper_seq_def by(auto simp add: map_comprehension_def)
              have eq1:"?C1.1 = [ j \<mapsto> (if_then_else ((\<lambda>j. \<lambda>s. prime (s c)) j) ((\<lambda>j. x ::= (\<lambda>s. 4 * s x) ;; i ::= (\<lambda>s. s i - 1)) j) ((\<lambda>j. Skip) j)) | j \<in> {1} ]"
                apply(rule)
                by(auto simp add:map_comprehension_def if_then_else_def if_then_else_skip_def)
              have eq2: "?C1.2 = [j \<mapsto> (\<lambda>j. c ::= (\<lambda>s. s c + 1)) j | j \<in> {1}]"
                apply(rule)
                by(auto simp add:map_comprehension_def)
              (*Step 4.1.2*)
              show "\<Turnstile> { conj (?Iv n) (conj (holds_for_prog_set J ?conds) (?V J))} [[i \<mapsto> ?bodies i | i \<in> J]] { ?Iv (Suc n) }"
                apply(simp only:eq)
                apply(rule lockstep_seq[where ?R="conj (?Iv n) (conj (holds_for_prog_set J ?conds) (?V J))"])
                 apply(simp only:eq1)
                 apply(rule precondition_conseq[where ?P'="conj (conj (?Iv n) (conj (holds_for_prog_set J ?conds) (?V J))) (holds_forall_hyper {1} (lnot_hyper (\<lambda>j. \<lambda>s. prime (s c))))"])
                  prefer 2
                  apply(rule if_lockstep_false)
                  apply(rule postcondition_conseq)
                   prefer 2
                   apply(rule skip_lockstep)
                  apply(intro entailsI)
                unfolding conj_def
                  apply meson
                 apply(intro entailsI)
                unfolding holds_for_prog_set_def holds_forall_hyper_def lnot_hyper_def
                 apply (smt (z3) \<open>J = {1}\<close> bot_nat_0.not_eq_extremum empty_iff insert_iff less_numeral_extra(1))
                apply(rule precondition_conseq)
                 prefer 2
                apply(simp only:eq2)
                 apply(rule assign_lockstep)
                apply(intro entailsI conjI impI)
                apply(erule conjE)+
                subgoal premises prems proof - show ?thesis using prems(1) assms(1) by(fastforce) qed
                apply(erule conjE)+
                subgoal premises prems proof - show ?thesis using prems(4) assms(1) by(fastforce) qed
                apply(erule conjE)+
                subgoal premises prems proof - show ?thesis using prems(5) assms(1) by(fastforce) qed
                 apply(erule conjE)+
                subgoal premises prems proof - show ?thesis using prems(6) assms(1) by(fastforce) qed
                apply(erule conjE)+
                subgoal premises prems proof - show ?thesis using prems(7) assms(1) by(fastforce) qed
                done
            next
              assume "J = {0, 1}"
              have eq:"[i \<mapsto> ?bodies i | i \<in> J] = hyper_seq ?LBs.1 ?LBs.2"
                apply(rule)
                using \<open>J = {0, 1}\<close>
                by(auto simp add:map_comprehension_def hyper_seq_def)
              have eq1:"?LBs.1 = [0 \<mapsto> x ::= (\<lambda>s. 4 * s x) ;; i ::= (\<lambda>s. s i - 1)] 
                            ++ [j \<mapsto> (\<lambda>j. IF \<lambda>s. prime (s c)  THEN x ::= (\<lambda>s. 4 * s x) ;; i ::= (\<lambda>s. s i - 1) ELSE Skip) j | j \<in> {1}]"
                apply(rule)
                by(auto simp add:map_add_def map_comprehension_def if_then_else_skip_def)
              have eq2: "[0 \<mapsto> x ::= (\<lambda>s. 4 * s x) ;; i ::= (\<lambda>s. s i - 1)] 
                            ++ [j \<mapsto> (\<lambda>j. x ::= (\<lambda>s. 4 * s x) ;; i ::= (\<lambda>s. s i - 1)) j | j \<in> {1}] = hyper_seq ?LBs1p1 ?LBs1p2"
                apply(rule)
                by(auto simp add:map_add_def map_comprehension_def hyper_seq_def)
              have eq3: "[0 \<mapsto> x ::= (\<lambda>s. 4 * s x), 1 \<mapsto>x ::= (\<lambda>s. 4 * s x)] = [j \<mapsto> (\<lambda>j. x ::= (\<lambda>s. 4 * s x)) j | j \<in> {0,1}]"
                apply(rule)
                by(auto simp add: map_comprehension_def)
              have eq4: "[0 \<mapsto> i ::= (\<lambda>s. s i - 1), 1 \<mapsto>i ::= (\<lambda>s. s i - 1)] = [j \<mapsto> (\<lambda>j. i ::= (\<lambda>s. s i - 1)) j | j \<in> {0,1}]"
                apply(rule)
                by(auto simp add: map_comprehension_def)
              have eq5: "[ 1 \<mapsto> c ::= (\<lambda>s. s c + 1)] = [j \<mapsto> (\<lambda>j. c ::= (\<lambda>s. s c + 1)) j | j \<in> {1}]"
                apply(rule)
                by(auto simp add: map_comprehension_def)
              (*Step 4.1.3*)
              show "\<Turnstile> { conj (?Iv n) (conj (holds_for_prog_set J ?conds) (?V J))} [[i \<mapsto> ?bodies i | i \<in> J]] { ?Iv (Suc n) }"
                apply(simp only:eq)
                apply(rule lockstep_seq[where ?R="(?Iv n)"])
                 apply(simp only:eq1)
                 apply(rule precondition_conseq)
                prefer 2
                  apply(rule if_lockstep_trueG[where ?P="conj (?Iv n) (conj (holds_for_prog_set J ?conds) (?V J))"])
                   prefer 2
                   apply(simp add:dom_def map_comprehension_def)
                  prefer 2
                  apply(rule entails_conj)
                  apply(intro entailsI)
                apply(simp)
                  apply(intro entailsI)
                unfolding conj_def holds_forall_hyper_def
                using \<open>J = {0, 1}\<close>
                  apply(simp add:conj_def)
                  apply fastforce
                 apply(simp only:eq2)
                 apply(rule lockstep_seq[where ?R = "(?Iv n)"])
                  apply(rule precondition_conseq)
                   prefer 2
                apply(simp only:eq3)
                apply(rule assign_lockstep)
                apply(intro entailsI allI impI conjI)
                apply(erule conjE)+
                subgoal premises prems proof - show ?thesis using prems(2) assms(1) by fastforce qed
                apply(erule conjE)+
                subgoal premises prems proof - show ?thesis using prems(5) assms(1) by fastforce qed
                apply(erule conjE)+
                subgoal premises prems proof - show ?thesis using prems(6) assms(1) by fastforce qed
                apply(erule conjE)+
                subgoal premises prems proof - show ?thesis using prems(7) assms(1) by fastforce qed
                apply(erule conjE)+
                subgoal premises prems proof - show ?thesis using prems(8) assms(1) by fastforce qed
                apply(simp only: eq4)
                 apply(rule precondition_conseq)
                  prefer 2
                  apply(rule assign_lockstep)
                 apply(intro entailsI allI impI conjI)
                 apply(erule conjE)+
                 subgoal premises prems proof - show ?thesis using prems(1) by fastforce qed
                 apply(erule conjE)+
                 subgoal premises prems proof - show ?thesis using prems(2) by fastforce  qed
                 apply(erule conjE)+
                 subgoal premises prems proof - show ?thesis using prems(3) by fastforce  qed
                 apply(erule conjE)+
                 subgoal premises prems proof - show ?thesis using prems(4) by fastforce  qed
                 apply(erule conjE)+
                 subgoal premises prems proof - show ?thesis using prems(5) assms(1) by fastforce qed
                 apply(simp only:eq5)
                 apply(rule precondition_conseq)
                  prefer 2
                  apply (rule assign_lockstep)
                 apply(intro entailsI conjI impI allI)
                 apply(erule conjE)+
                 subgoal premises prems proof - show ?thesis using prems(1) assms(1) by fastforce qed
                 apply(erule conjE)+
                 subgoal premises prems proof - show ?thesis using prems(2) assms(1) by fastforce  qed
                 apply(erule conjE)+
                 subgoal premises prems proof - show ?thesis using prems(3) assms(1) by fastforce  qed
                 apply(erule conjE)+
                 subgoal premises prems proof - show ?thesis using prems(4) by fastforce  qed
                 apply(erule conjE)+
                 subgoal premises prems proof - show ?thesis using prems(5) assms(1) by fastforce qed
                 done           
            qed
          qed
        next
          (*Step 4.2*)
          show "\<forall>n. entails (?Iv n) (all_unfinished_can_be_stepped_after n ?Iv {0,1} ?conds ?V)" 
          proof
            fix n::nat
            from bigger_prime obtain n' where "n \<le> n'" and "prime n'" 
              using order_less_imp_le by blast
            show "entails (?Iv n) (all_unfinished_can_be_stepped_after n ?Iv {0,1} ?conds ?V)"
            proof(intro allI ballI impI entailsI conjI exI)
              from \<open>n \<le> n'\<close> show "n \<le> n'" by auto
            next
              fix S 
              fix i'::nat
              fix S'
              assume "?Iv n S" and "?Iv n' S'" and "i' \<in> {0,1}" and hfa:"\<not> holds_forall (lnot (\<lambda>s. 0 < s i)) (S' i')"
              from \<open>?Iv n' S'\<close> hfa have H1: "(holds_for_prog_set {0,1} (\<lambda>j s. 0 < s i)) S'" 
                unfolding holds_for_prog_set_def holds_forall_def lnot_def holds_forall_hyper_def
                using \<open>i' \<in> {0, 1}\<close>
                by (metis empty_iff insert_iff)
              from \<open>?Iv n' S'\<close>  \<open>prime n'\<close> have H2: "\<forall>\<sigma>1\<in>S' 1. prime (snd \<sigma>1 c)" by fastforce
              show "\<exists>J\<in>Pow {0, 1}. i' \<in> J \<and> conj (holds_for_prog_set J (\<lambda>j s. 0 < s i))
                (if J = {0, 1} then \<lambda>S. \<forall>\<sigma>1\<in>S 1. prime (snd \<sigma>1 c)
                 else if J = {1} then \<lambda>S. \<forall>\<sigma>1\<in>S 1. \<not> prime (snd \<sigma>1 c) else (\<lambda>S. False))
                  S'"
              proof 
                show "i' \<in> {0,1} \<and> conj (holds_for_prog_set {0,1} (\<lambda>j s. 0 < s i))
                (if {0,1} = {0, 1} then \<lambda>S. \<forall>\<sigma>1\<in>S 1. prime (snd \<sigma>1 c) else if {0,1} = {1} then \<lambda>S. \<forall>\<sigma>1\<in>S 1. \<not> prime (snd \<sigma>1 c) else (\<lambda>S. False)) S'"
                  using H1 H2 \<open>i' \<in> {0,1}\<close>
                  by(auto simp add:conj_def)
              next
                show "{0, 1} \<in> Pow {0, 1} " by auto
              qed
            qed
          qed
        next
          (*Step 4.3*)
          show "\<forall>n. entails (?Iv n) (can_step_subset_or_all_finished {0,1} ?conds ?V)" 
          proof(intro allI entailsI)
            fix n S
            assume asm:"?Iv n S"
            from asm have "(\<forall>\<sigma>0\<in>S 0. \<not>(0 < snd \<sigma>0 i)) \<and> (\<forall>\<sigma>1\<in>S 1. \<not>(0 < snd \<sigma>1 i)) \<or> (\<forall>\<sigma>0\<in>S 0. (0 < snd \<sigma>0 i)) \<and> (\<forall>\<sigma>1\<in>S 1. (0 < snd \<sigma>1 i))"
              by metis
            thus "(can_step_subset_or_all_finished {0,1} ?conds ?V) S" 
            proof
              assume asm:"(\<forall>\<sigma>0\<in>S 0. \<not>(0 < snd \<sigma>0 i)) \<and> (\<forall>\<sigma>1\<in>S 1. \<not>(0 < snd \<sigma>1 i))"
              show ?thesis
                unfolding disj_def
                apply (rule disjI2)
                unfolding holds_forall_hyper_def lnot_hyper_def
                using asm
                by(auto)
            next
              assume asm1: "(\<forall>\<sigma>0\<in>S 0. 0 < snd \<sigma>0 i) \<and> (\<forall>\<sigma>1\<in>S 1. 0 < snd \<sigma>1 i)"
              from asm have "(\<forall>\<sigma>1\<in>S 1. prime ((snd \<sigma>1) c)) \<or> (\<forall>\<sigma>1\<in>S 1. \<not>prime ((snd \<sigma>1) c))" by auto
              thus ?thesis
              proof(rule)
                assume asm2: "\<forall>\<sigma>1\<in>S 1. prime (snd \<sigma>1 c)"
                with asm1 have "(\<forall>\<sigma>0\<in>S 0. 0 < snd \<sigma>0 i) \<and> (\<forall>\<sigma>1\<in>S 1. 0 < snd \<sigma>1 i) \<and> (\<forall>\<sigma>1\<in>S 1. prime (snd \<sigma>1 c))" by auto
                show ?thesis unfolding disj_def disj_I_def conj_def holds_for_prog_set_def holds_forall_hyper_def
                  apply (rule disjI1)
                proof
                  from asm1 asm2 show "(\<forall>ia\<in>{0,1}. \<forall>\<phi>\<in>S ia. 0 < snd \<phi> i) \<and> (if {0,1} = {0, 1} then \<lambda>S. \<forall>\<sigma>1\<in>S 1. prime (snd \<sigma>1 c) else if {0,1} = {1} then \<lambda>S. \<forall>\<sigma>1\<in>S 1. \<not> prime (snd \<sigma>1 c) else (\<lambda>S. False)) S"
                    by simp
                next 
                  show "{0, 1} \<in> Pow {0, 1} - {{}}" by auto
                qed
              next
                assume asm2: "\<forall>\<sigma>1\<in>S 1. \<not> prime (snd \<sigma>1 c)"
                with asm1 have "(\<forall>\<sigma>1\<in>S 1. 0 < snd \<sigma>1 i) \<and> (\<forall>\<sigma>1\<in>S 1. \<not>prime (snd \<sigma>1 c))" by auto
                show ?thesis unfolding disj_def disj_I_def conj_def holds_for_prog_set_def holds_forall_hyper_def
                  apply (rule disjI1)
                proof
                  from asm1 asm2 show "(\<forall>ia\<in>{1::nat}. \<forall>\<phi>\<in>S ia. 0 < snd \<phi> i) \<and> (if {1::nat} = {0, 1} then \<lambda>S. \<forall>\<sigma>1\<in>S 1. prime (snd \<sigma>1 c) else if {1} = {1} then \<lambda>S. \<forall>\<sigma>1\<in>S 1. \<not> prime (snd \<sigma>1 c) else (\<lambda>S. False)) S"
                    by(auto)
                next
                  show "{1} \<in> Pow {0, 1} - {{}}" by auto
                qed
              qed
            qed
          qed
        next
          (*Step 4.4*)
          show "\<forall>n. \<Turnstile> { (?Iv n)} [[i \<mapsto> Assume (lnot (?conds i)) | i \<in> {0,1}]] { ?Q }" 
            apply(intro allI)
            apply(rule precondition_conseq[where ?P'="(\<lambda>S::nat hyper_set. (\<forall>\<sigma>0 \<in> (S 0). \<exists>\<sigma>1 \<in> (S 1). (snd \<sigma>0 x) = (snd \<sigma>1 x) \<and> (snd \<sigma>0 i) = (snd \<sigma>1 i)))"])
             apply(intro entailsI)
             apply fastforce
            apply(rule precondition_conseq)
            prefer 2
             apply(rule assume_lockstep)
            apply(intro entailsI)
            unfolding lnot_def
            by fastforce
        next 
          (*Step 4.5*)
          show "relational_upwards_closed {0, 1} (\<lambda>n. ?Q) ?Q" 
            apply(auto simp add:relational_upwards_closed_def hyper_union_def hyper_ascending_def hyper_set_le_def)
            by (metis snd_eqD)
        qed
      qed
    qed
  qed
qed



end