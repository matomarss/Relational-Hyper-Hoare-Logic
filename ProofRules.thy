text \<open>3 Proof rules\<close>
theory ProofRules
  imports LogicRHHL
begin

section\<open>Preliminaries\<close>

text\<open>Map comprehension\<close>
definition map_comprehension :: "('i \<Rightarrow> 'a) \<Rightarrow> ('i \<Rightarrow> bool) \<Rightarrow> ('i \<rightharpoonup> 'a)" where
  "map_comprehension f P \<equiv> (\<lambda>i. if P i then Some (f i) else None)"

translations
  "[i \<mapsto> t | P]" => "CONST map_comprehension (\<lambda>i. t) (\<lambda>i. P)"

text\<open>Hyper sequence\<close>
fun seq_opt where
  "seq_opt (Some C1) (Some C2) = Some (C1;; C2)"
| "seq_opt (Some C1) None = Some C1"
| "seq_opt None r = r"

definition hyper_seq (infixr ";;\<^sub>H" 60) where
  "hyper_seq Cs Cs' n = seq_opt (Cs n) (Cs' n)"

lemma sem_lifted_hyper_seq:
  "sem_rel Cs' (sem_rel Cs S) = sem_rel (hyper_seq Cs Cs') S"
  unfolding sem_rel_def hyper_seq_def
  apply (rule ext)
  apply (case_tac "Cs i"; case_tac "Cs' i")
     apply simp_all
  using sem_seq by blast

text\<open>\<box>_I p\<close>
definition holds_forall_hyper where
  "holds_forall_hyper I bs S \<longleftrightarrow> (\<forall>i\<in>I. \<forall>\<phi>\<in>(S i). (bs i) (snd \<phi>))"

text\<open>low_I p\<close>
definition low_exp_hyper where
  "low_exp_hyper I es S = (\<forall>i\<in>I. \<forall>i'\<in>I. \<forall>\<phi> \<phi>'. (\<phi> \<in> (S i) \<and> \<phi>' \<in> (S i')) \<longrightarrow> ((es i) (snd \<phi>) = (es i') (snd \<phi>')))"

text\<open>(\<not>b)(i)(\<sigma>) \<triangleq> \<not>(b(i)(\<sigma>))\<close>
definition lnot_hyper where
  "lnot_hyper bs i \<sigma> = (\<not>(bs i) \<sigma>)"

lemma low_exp_either: "(low_exp_hyper I bs) S \<Longrightarrow> (holds_forall_hyper I bs S) \<or> (holds_forall_hyper I (lnot_hyper bs) S)"
  by (smt (verit) holds_forall_hyper_def lnot_hyper_def low_exp_hyper_def)

lemma either_low_exp: "(holds_forall_hyper I bs S) \<or> (holds_forall_hyper I (lnot_hyper bs) S) \<Longrightarrow> low_exp_hyper I bs S"
  by (smt (verit, del_insts) holds_forall_hyper_def lnot_hyper_def low_exp_hyper_def)

corollary low_exp_equiv: "(low_exp_hyper I bs) = disj (holds_forall_hyper I bs) (holds_forall_hyper I (lnot_hyper bs))"
  unfolding disj_def
  apply(rule)
  using low_exp_either either_low_exp by blast

text\<open>Definitions of \<box>_i p and (\<not>b)(\<sigma>) can be found in HHL/Loops as holds_forall and lnot\<close>

text\<open>Definitions of conjunction, disjunction and entailment of hyper-assertions and also relational hyper-assertions can be found in 
     HHL/Logic as conj, disj and entails\<close>

text\<open>Defintions of the if-else and while commands you can find in HHL/Loops as if_then_else and while_cond\<close>

text\<open>Definition of the if command
    - the missing else branch is represented with the Skip command\<close>
definition if_then_else_skip where
"if_then_else_skip b C = if_then_else b C Skip "

notation if_then_else  ("IF _ THEN _ ELSE _" [0, 0, 61] 61)
notation if_then_else_skip  ("IF _  THEN _ FI" [0, 60] 61)
notation while_cond  ("WHILE _ DO _" [0, 61] 61)


section \<open>3.2 Basic rules\<close>
subsection \<open>3.2.1 Consequence and true-false rules\<close>
theorem cons:
  assumes "entails P P'"
      and "entails Q' Q"
      and "\<Turnstile> {P'} [C] {Q'}"
    shows "\<Turnstile> {P} [C] {Q}"
  by (metis assms(1,2,3) entails_def relational_hyper_hoare_triple_def)

corollary cons_prec:
  assumes "entails P P'"
      and "\<Turnstile> {P'} [C] {Q}"
    shows "\<Turnstile> {P} [C] {Q}"
  apply(rule cons)
  using assms apply simp
   apply(rule entails_refl)
  using assms by simp

corollary cons_post:
  assumes "entails Q' Q"
      and "\<Turnstile> {P} [C] {Q'}"
    shows "\<Turnstile> {P} [C] {Q}"
  apply(rule cons)
   apply(rule entails_refl)
  using assms apply simp
  using assms by simp


theorem false:
  shows "\<Turnstile> {(\<lambda>S. False)} [Cs] {Q}"
proof (intro relational_hyper_hoare_tripleI)
  fix S
  assume "False"
  thus "Q (sem_rel Cs S)" by auto
qed

theorem true:
  shows "\<Turnstile> {P} [Cs] {(\<lambda>S. True)}"
  by (simp add: relational_hyper_hoare_tripleI)


subsection\<open>3.2.2 Lockstep rules\<close>

abbreviation assign_hyper_set where
"assign_hyper_set I Xs Es S \<equiv> (\<lambda>i. (if i \<in> I then { (l, \<sigma>((Xs i) := (Es i) \<sigma>)) |l \<sigma>. (l, \<sigma>) \<in> (S i) } else S i))"

abbreviation assign_prec where
"assign_prec P I Xs Es S \<equiv> P (assign_hyper_set I Xs Es S)"

theorem assign_lockstep:
  shows "\<Turnstile>  { assign_prec P I Xs Es} [[i \<mapsto> Assign (Xs i) (Es i) |i \<in> I]] {P}"
proof (rule relational_hyper_hoare_tripleI)
  fix S
  assume asm: "assign_prec P I Xs Es S"
  have "assign_hyper_set I Xs Es S = (sem_rel [i \<mapsto> Assign (Xs i) (Es i) |i \<in> I] S)"
  proof
    fix i
    show "assign_hyper_set I Xs Es S i = (sem_rel [i \<mapsto> Assign (Xs i) (Es i) |i \<in> I] S) i"
      by(auto simp add:sem_rel_def map_comprehension_def sem_def intro:SemAssign)
  qed
  with asm show "P (sem_rel [i \<mapsto> Assign (Xs i) (Es i) |i \<in> I] S)" by auto
qed


abbreviation assume_hyper_set where
"assume_hyper_set I Bs S \<equiv> (\<lambda>i. (if i \<in> I then { (l, \<sigma>) |l \<sigma>. (l, \<sigma>) \<in> (S i) \<and> (Bs i) \<sigma>} else S i))"

abbreviation assume_prec where
"assume_prec P I Bs S \<equiv> P (assume_hyper_set I Bs S)"

theorem assume_lockstep:
  shows "\<Turnstile>  { assume_prec P I Bs} [[i \<mapsto> Assume (Bs i) |i \<in> I]] {P}"
proof (rule relational_hyper_hoare_tripleI)
  fix S
  assume asm: "assume_prec P I Bs S"
  have "(assume_hyper_set I Bs S) = (sem_rel [i \<mapsto> Assume (Bs i) |i \<in> I] S)"
  proof
    fix i
    show "(assume_hyper_set I Bs S) i = (sem_rel [i \<mapsto> Assume (Bs i) |i \<in> I] S) i"
      by(auto simp add:sem_rel_def map_comprehension_def sem_def intro:SemAssume)
  qed
  with asm show "P (sem_rel [i \<mapsto> Assume (Bs i) |i \<in> I] S)" by auto
qed


abbreviation havoc_hyper_set where
"havoc_hyper_set I Xs S \<equiv> (\<lambda>i. (if i \<in> I then { (l, \<sigma>((Xs i) := v)) |l \<sigma> v. (l, \<sigma>) \<in> (S i) } else S i))"

abbreviation havoc_prec where
"havoc_prec P I Xs S \<equiv> P (havoc_hyper_set I Xs S)"

theorem havoc_lockstep:
  shows "\<Turnstile>  { havoc_prec P I Xs } [[i \<mapsto> Havoc (Xs i) |i \<in> I]] {P}"
proof (rule relational_hyper_hoare_tripleI)
  fix S
  assume asm: "havoc_prec P I Xs S"
  have "havoc_hyper_set I Xs S = (sem_rel [i \<mapsto> Havoc (Xs i) |i \<in> I] S)"
  proof
    fix i
    show "havoc_hyper_set I Xs S i = (sem_rel [i \<mapsto> Havoc (Xs i) |i \<in> I] S) i"
      by(auto simp add:sem_rel_def map_comprehension_def sem_def intro:SemHavoc)
  qed
  with asm show "P (sem_rel [i \<mapsto> Havoc (Xs i) |i \<in> I] S)" by auto
qed


theorem skip_lockstep:
  shows "\<Turnstile> {P} [[i \<mapsto> Skip |i \<in> I]] {P}"
proof (rule relational_hyper_hoare_tripleI)
  fix S
  assume "P S"
  have eq:"(sem_rel (map_comprehension (\<lambda>i. Skip) (\<lambda>i. i \<in> I)) S) = S"
    apply(rule) using SemSkip
    by(auto simp add:sem_rel_def map_comprehension_def sem_def)
  show "P (sem_rel (map_comprehension (\<lambda>i. Skip) (\<lambda>i. i \<in> I)) S)"
    apply(simp only:eq) using \<open>P S\<close> by auto
qed


subsection\<open>3.2.3 Extension and associativity rules\<close>

lemma sem_lifted_on_disjoint_maps_seq:
  assumes "dom Cs \<inter> dom Cs' = {}"
  shows "sem_rel (Cs ++ Cs') S = sem_rel Cs' (sem_rel Cs S)"
  unfolding sem_rel_def
  by (metis (no_types, opaque_lifting) assms disjoint_insert(1) domIff insert_absorb map_add_dom_app_simps(1) map_add_dom_app_simps(3) partial_sem.simps(2))

theorem rel_extension:
  assumes "\<Turnstile> { P } [ Cs ] { R }"
      and "\<Turnstile> { R } [ Cs' ] { Q }"
      and "dom Cs \<inter> dom Cs' = {}"
    shows "\<Turnstile> { P } [ Cs ++ Cs' ] { Q }"
proof (rule relational_hyper_hoare_tripleI)
  fix S assume "P S"
  then show "Q (sem_rel (Cs ++ Cs') S)"
    by (metis assms(1) assms(2) assms(3) relational_hyper_hoare_triple_def sem_lifted_on_disjoint_maps_seq)
qed


theorem seq_extension:
  assumes "\<Turnstile> { P } [ Cs ] { R }"
      and "\<Turnstile> { R } [ Cs' ] { Q }"
    shows "\<Turnstile> { P } [ hyper_seq Cs Cs' ] { Q }"
proof (rule relational_hyper_hoare_tripleI)
  fix S assume "P S"
  then have "R (sem_rel Cs S)"
    by (meson assms(1) relational_hyper_hoare_triple_def)
  then have "Q (sem_rel Cs' (sem_rel Cs S))"
    by (meson assms(2) relational_hyper_hoare_triple_def)
  then show "Q (sem_rel (hyper_seq Cs Cs') S)"
    by (simp add: sem_lifted_hyper_seq)
qed


text\<open>Proof that RelExt is a corollary of SeqExt\<close>
corollary rel_extension_by_seq_extension:
  assumes "\<Turnstile> { P } [ Cs ] { R }"
      and "\<Turnstile> { R } [ Cs' ] { Q }"
      and "dom Cs \<inter> dom Cs' = {}"
    shows "\<Turnstile> { P } [ Cs ++ Cs' ] { Q }"
proof -
  have "Cs ++ Cs' = hyper_seq Cs Cs'"
    unfolding hyper_seq_def map_add_def
    apply(rule)
    apply(auto split:option.split)
     apply (metis option.collapse seq_opt.simps(2,3))
    using assms(3)
    by (metis disjoint_iff_not_equal domI domIff seq_opt.simps(3))
  with seq_extension show ?thesis using assms(1) assms(2) by auto
qed


text\<open>Another corollary of the seq_extension rule used for stepping only a single program.\<close>
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
  ultimately show "Q (sem_rel Cs S)"
    using seq_extension[of P "[i \<mapsto> C1]" R "Cs(i \<mapsto> C2)" Q]
    by (metis assms(2) assms(3) relational_hyper_hoare_triple_def)
qed



lemma seq_associativity_main:
  shows "sem_rel (Cs1;;\<^sub>HCs2;;\<^sub>HCs3) S = sem_rel ((Cs1;;\<^sub>HCs2);;\<^sub>HCs3) S"
proof 
  fix i
  show "sem_rel (Cs1 ;;\<^sub>H Cs2 ;;\<^sub>H Cs3) S i = sem_rel ((Cs1 ;;\<^sub>H Cs2) ;;\<^sub>H Cs3) S i"
    apply(auto simp add:sem_rel_def hyper_seq_def)
     apply(cases "Cs1 i")
      apply(auto)
     apply(cases "Cs2 i")
      apply(auto)
     apply(cases "Cs3 i")
      apply(auto simp add:sem_def)
    using SemSeq apply blast
     apply(cases "Cs1 i")
      apply(auto)
     apply(cases "Cs2 i")
      apply(auto)
     apply(cases "Cs3 i")
      apply(auto simp add:sem_def)
    using SemSeq apply blast
    done
qed
  

theorem seq_associativity:
  shows "\<Turnstile> {P} [Cs1;;\<^sub>HCs2;;\<^sub>HCs3] {Q} = \<Turnstile> {P} [(Cs1;;\<^sub>HCs2);;\<^sub>HCs3] {Q} "
  unfolding relational_hyper_hoare_triple_def
  by(simp only: seq_associativity_main)



subsection \<open>3.2.4 Syntactic rules\<close>

subsubsection\<open>AssumeS\<close>

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

lemma sem_lifted_map_zero:
  "sem_rel [0 \<mapsto> C] S = map_zero (sem C) S"
  unfolding sem_rel_def
  apply (rule ext)
  by (case_tac i) simp_all

lemma rule_assume_syntactic_general:
  "\<Turnstile> { sat_assertion vals states (transform_assume (pbexp_to_assertion 0 pb) P) } [ [0 \<mapsto> Assume (interp_pbexp pb)] ] {sat_assertion vals states P}"
proof (rule relational_hyper_hoare_tripleI)
  fix S assume asm0: "sat_assertion vals states (transform_assume (pbexp_to_assertion 0 pb) P) S"
  then have "sat_assertion vals states P (map_zero (Set.filter (interp_pbexp pb \<circ> snd)) S)"
    using pexp_to_exp_same transform_assume_valid by blast
  then show "sat_assertion vals states P (sem_rel [0 \<mapsto> Assume (interp_pbexp pb)] S)"
  proof -
    have "\<forall>p r. sem (Assume p) (r::((nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a)) set) = Set.filter (p \<circ> snd) r"
      using assume_sem by blast
    then have "sat_assertion vals states P (map_zero (sem (Assume (interp_pbexp pb))) S)"
      using \<open>sat_assertion vals states P (map_zero (Set.filter (interp_pbexp pb \<circ> snd)) S)\<close> by presburger
    then show ?thesis by (simp add: sem_lifted_map_zero)
  qed
qed

theorem assumeS_rel:
  "\<Turnstile> { interp_assert (transform_assume (pbexp_to_assertion 0 pb) P) } [ [0 \<mapsto> Assume (interp_pbexp pb)] ] {interp_assert P}"
  by (simp add: rule_assume_syntactic_general)


subsubsection\<open>HavocS\<close>

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


lemma rule_havoc_syntactic_general:
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
  then show "sat_assertion states vals P (sem_rel [0 \<mapsto> Havoc x] S)"
    by (simp add: asm0 sem_lifted_map_zero)
qed


theorem havocS_rel:
  "\<Turnstile> { interp_assert (transform_havoc x P) } [ [0 \<mapsto> Havoc x] ] {interp_assert P}"
  by (simp add: rule_havoc_syntactic_general)



subsubsection\<open>AssignS\<close>

text \<open>Program expressions\<close>
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


text \<open>Expressions (Boolean and values)\<close>
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



text \<open>Assertions\<close>
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


lemma rule_assign_syntactic_general:
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
  then show "sat_assertion vals states P (sem_rel [0 \<mapsto> Assign x (interp_pexp pe)] S)"
    by (simp add: sem_lifted_map_zero)
qed



theorem assignS_rel:
  "\<Turnstile> { interp_assert (transform_assign x pe P) } [ [0 \<mapsto> Assign x (interp_pexp pe)] ] {interp_assert P}"
  by (simp add: rule_assign_syntactic_general)








section\<open>3.3 Synchronized rules for if\<close> 

subsection\<open>Conditional rewrite rule\<close>
text\<open>The conditional rewrite rule from the appendix. Used only for proofs in this section.\<close>

definition sem_equiv_hyper_cond where
"sem_equiv_hyper_cond Cs1 Cs2 P \<longleftrightarrow> (\<forall>S. P S \<longrightarrow> (sem_rel Cs1 S) = (sem_rel Cs2 S))"

lemma sem_equiv_hyper_cond_refl:
  "sem_equiv_hyper_cond Cs1 Cs2 P = sem_equiv_hyper_cond Cs2 Cs1 P"
  unfolding sem_equiv_hyper_cond_def by auto

theorem rewrite_rule_cond:
  assumes "sem_equiv_hyper_cond Cs1 Cs2 P"
      and "\<Turnstile> {P} [Cs1] {Q}" 
    shows "\<Turnstile> {P} [Cs2] {Q}"
  using assms
  by(auto simp add:relational_hyper_hoare_triple_def sem_rel_def sem_equiv_hyper_cond_def)

lemma sem_rel_rewrite: "sem_rel [ i \<mapsto> (C i) | i \<in> I ] S = (\<lambda>i. if (i \<in> I) then (sem (C i) (S i)) else (S i))"
  by (metis (mono_tags, lifting) map_comprehension_def partial_sem.simps(1,2) sem_rel_def) 

lemma sem_equiv_hyper_cond_extend:
  assumes "sem_equiv_hyper_cond Cs1 Cs2 P"
      and "dom Cs' \<inter> dom Cs1 = {}"
      and "dom Cs' \<inter> dom Cs2 = {}"
    shows "sem_equiv_hyper_cond (Cs' ++ Cs1) (Cs' ++ Cs2 )P"
proof(auto simp add:sem_equiv_hyper_cond_def)
  fix S
  assume "P S"
  show "sem_rel (Cs' ++ Cs1) S = sem_rel (Cs' ++ Cs2) S "
    apply(rule)
    using assms
    apply(auto simp add:sem_rel_def map_add_def sem_equiv_hyper_cond_def dom_def)
     apply (metis \<open>P S\<close> assms(2,3) inf_commute map_add_comm map_add_def sem_rel_def sem_lifted_on_disjoint_maps_seq)
    by (metis \<open>P S\<close> assms(2,3) inf_commute map_add_comm map_add_def sem_rel_def sem_lifted_on_disjoint_maps_seq)
qed


subsection\<open>IfTrueLck\<close>
theorem if_true_lck:
  assumes "\<Turnstile> { conj P (holds_forall_hyper I bs) } [Cs' ++ [i \<mapsto> (Cs1 i) | i \<in> I]] { Q }"
      and "dom Cs' \<inter> I = {}"
  shows "\<Turnstile> { conj P (holds_forall_hyper I bs)} [Cs' ++ [ i \<mapsto> (if_then_else (bs i) (Cs1 i) (Cs2 i)) | i \<in> I ]] { Q }"
proof -
  have "sem_equiv_hyper_cond (Cs' ++ [i \<mapsto> (Cs1 i) | i \<in> I]) (Cs' ++[ i \<mapsto> (if_then_else (bs i) (Cs1 i) (Cs2 i)) | i \<in> I ]) (conj P (holds_forall_hyper I bs))"
    apply(auto simp add:holds_forall_hyper_def sem_equiv_hyper_cond_def conj_def snd_def map_add_def map_comprehension_def)
    apply(rule ext)
    apply(auto simp add:sem_rel_def sem_def if_then_else_def lnot_def)
    apply (metis SemAssume SemIf1 SemSeq case_prod_conv)
    by auto
  with assms rewrite_rule_cond show "\<Turnstile> { conj P (holds_forall_hyper I bs)} [Cs' ++ [ i \<mapsto> (if_then_else (bs i) (Cs1 i) (Cs2 i)) | i \<in> I ]] { Q }" by blast
qed


subsection\<open>IfFalseLck\<close>
theorem if_false_lck:
  assumes "\<Turnstile> { conj P (holds_forall_hyper I (lnot_hyper bs)) } [Cs' ++ [i \<mapsto> (Cs2 i) | i \<in> I]] { Q }"
      and "dom Cs' \<inter> I = {}"
  shows "\<Turnstile> { conj P (holds_forall_hyper I (lnot_hyper bs))} [Cs' ++ [ i \<mapsto> (if_then_else (bs i) (Cs1 i) (Cs2 i)) | i \<in> I ]] { Q }"
proof -
  have "sem_equiv_hyper_cond (Cs' ++ [i \<mapsto> (Cs2 i) | i \<in> I]) (Cs' ++[ i \<mapsto> (if_then_else (bs i) (Cs1 i) (Cs2 i)) | i \<in> I ]) (conj P (holds_forall_hyper I (lnot_hyper bs)))"
    apply(auto simp add:holds_forall_hyper_def lnot_hyper_def sem_equiv_hyper_cond_def conj_def snd_def map_add_def map_comprehension_def)
    apply(rule ext)
    apply(auto simp add:sem_rel_def sem_def if_then_else_def lnot_def)
    by (metis SemAssume SemIf2 SemSeq case_prod_conv lnot_def)
  with assms rewrite_rule_cond show "\<Turnstile> { conj P (holds_forall_hyper I (lnot_hyper bs))} [Cs' ++ [ i \<mapsto> (if_then_else (bs i) (Cs1 i) (Cs2 i)) | i \<in> I ]] { Q }" by blast
qed


subsection\<open>IfSyncLck\<close>
text\<open> A rule to progress all if statements in a lockstep given all executions will either take the first branch
or will all take the second branch.
Rule based directly on if_synchronized from HHL which translates directly into IfSync rule from the paper.
Uses the combination of total functions and a set of indices I to represent partial functions.
\<close>
theorem if_sync_lck:
  assumes "\<Turnstile> { conj P (holds_forall_hyper I bs) } [Cs' ++ [i \<mapsto> (Cs1 i) | i \<in> I]] { Q }"
    and   "\<Turnstile> { conj P (holds_forall_hyper I (lnot_hyper bs)) } [Cs' ++ [i \<mapsto> (Cs2 i) | i \<in> I]] { Q }"
      and "dom Cs' \<inter> I = {}"
    shows "\<Turnstile> { conj P (low_exp_hyper I bs)} [Cs' ++ [ i \<mapsto> (if_then_else (bs i) (Cs1 i) (Cs2 i)) | i \<in> I ]] { Q }"
proof -
  from if_true_lck assms(1) assms(3) have "\<Turnstile> { conj P (holds_forall_hyper I bs)} [Cs' ++ [ i \<mapsto> (if_then_else (bs i) (Cs1 i) (Cs2 i)) | i \<in> I ]] { Q }"
    by (simp add: if_true_lck)
  moreover from if_false_lck assms(2) assms(3) have "\<Turnstile> { conj P (holds_forall_hyper I (lnot_hyper bs))} [Cs' ++ [ i \<mapsto> (if_then_else (bs i) (Cs1 i) (Cs2 i)) | i \<in> I ]] { Q }"
    by (simp add: if_false_lck)
  ultimately show ?thesis 
    unfolding relational_hyper_hoare_triple_def
  proof (intro ballI allI impI)
    fix S
    assume asm1:"\<forall>S. Logic.conj P (holds_forall_hyper I bs) S \<longrightarrow>
              Q (sem_rel (Cs' ++ map_comprehension (\<lambda>i. if_then_else (bs i) (Cs1 i) (Cs2 i)) (\<lambda>i. i \<in> I)) S)" and
          asm2:"\<forall>S. Logic.conj P (holds_forall_hyper I (lnot_hyper bs)) S \<longrightarrow>
              Q (sem_rel (Cs' ++ map_comprehension (\<lambda>i. if_then_else (bs i) (Cs1 i) (Cs2 i)) (\<lambda>i. i \<in> I)) S)" and
          asm3:"Logic.conj P (low_exp_hyper I bs) S"
    hence "conj P (holds_forall_hyper I bs) S \<or> conj P (holds_forall_hyper I (lnot_hyper bs)) S" using low_exp_either conj_def by metis
    thus "Q (sem_rel (Cs' ++ map_comprehension (\<lambda>i. if_then_else (bs i) (Cs1 i) (Cs2 i)) (\<lambda>i. i \<in> I)) S)"
    proof
      assume "Logic.conj P (holds_forall_hyper I bs) S"
      with asm1 show ?thesis by auto
    next 
      assume "Logic.conj P (holds_forall_hyper I (lnot_hyper bs)) S"
      with asm2 show ?thesis by auto
    qed
  qed
qed


subsection\<open>IfSyncLckArb\<close>

abbreviation pick_branch where
"pick_branch P bs Cs1 Cs2 i  \<equiv> (if (entails P (\<lambda>S. (holds_forall (bs i) (S i)))) then (Cs1 i) else (Cs2 i))"


lemma if_equiv:
    shows "(let bs'  = (\<lambda>i. if entails P (\<lambda>S. holds_forall (bs i) (S i))
                  then bs i else lnot_hyper bs i);
         Cs1' = (\<lambda>i. if entails P (\<lambda>S. holds_forall (bs i) (S i))
                  then Cs1 i else Cs2 i);
         Cs2' = (\<lambda>i. if entails P (\<lambda>S. holds_forall (bs i) (S i))
                  then Cs2 i else Cs1 i)
     in  sem_equiv_hyper_cond [ i \<mapsto> if_then_else (bs' i) (Cs1' i) (Cs2' i) | i \<in> I ]
                         [ i \<mapsto> if_then_else (bs i) (Cs1 i) (Cs2 i) | i \<in> I ] P)"
  apply(auto simp add:entails_def holds_forall_def lnot_def sem_equiv_hyper_cond_def snd_def if_then_else_def sem_rel_rewrite)
  apply(rule ext)
  apply(auto simp add:sem_def)
  apply (metis SemAssume SemIf2 SemSeq lnot_def lnot_hyper_def)
  apply (metis SemAssume SemIf1 SemSeq lnot_def lnot_hyper_def)
  apply (metis SemAssume SemIf2 SemSeq lnot_def lnot_hyper_def)
  by (metis SemAssume SemIf1 SemSeq lnot_def lnot_hyper_def)


text\<open>
Generalization of the lockstep rules before. 
Executions of different programs can take different branches with this rule. 
\<close>
theorem if_sync_lck_arb:
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
  from assms if_equiv have equiv:"sem_equiv_hyper_cond [ i \<mapsto> if_then_else (?bs' i) (?Cs1' i) (?Cs2' i) | i \<in> I ]
                         [ i \<mapsto> if_then_else (bs i) (Cs1 i) (Cs2 i) | i \<in> I ] P" by auto
  with sem_equiv_hyper_cond_extend dif1 dif2 have equiv:"sem_equiv_hyper_cond( Cs' ++ [ i \<mapsto> if_then_else (?bs' i) (?Cs1' i) (?Cs2' i) | i \<in> I ])
                         (Cs' ++ [ i \<mapsto> if_then_else (bs i) (Cs1 i) (Cs2 i) | i \<in> I ]) P" by auto
  from assms(1) have hfa:"entails P (holds_forall_hyper I ?bs')"
    by(auto simp add:entails_def holds_forall_def holds_forall_hyper_def lnot_def lnot_hyper_def)
  hence ent_conj:"entails P (conj P (holds_forall_hyper I ?bs'))"
    by (metis (lifting) entail_conj entails_def)
  have "\<Turnstile> {conj P (holds_forall_hyper I ?bs')} [Cs' ++ [ i \<mapsto> if_then_else (?bs' i) (?Cs1' i) (?Cs2' i) | i \<in> I ]] {Q}" 
    apply(rule if_true_lck)
    apply(rule cons_prec)
    prefer 2
    using assms(2) apply(simp)
     apply (simp add: entail_conj_weaken)
    using assms by auto
  with ent_conj cons_prec have "\<Turnstile> {P} [Cs' ++ [ i \<mapsto> if_then_else (?bs' i) (?Cs1' i) (?Cs2' i) | i \<in> I ]] {Q}" by auto
  with equiv rewrite_rule_cond show ?thesis by auto
qed


subsection\<open>Simple corollaries\<close>
corollary if_true_lck_simp:
  assumes "\<Turnstile> { conj P (holds_forall_hyper I bs) } [[i \<mapsto> (Cs1 i) | i \<in> I]] { Q }"
    shows "\<Turnstile> { conj P (holds_forall_hyper I bs)} [[ i \<mapsto> (if_then_else (bs i) (Cs1 i) (Cs2 i)) | i \<in> I ]] { Q }"
proof -
  let ?Cs' = "\<lambda>i. None"
  from if_true_lck[where Cs'="?Cs'"] assms show ?thesis
    by fastforce
qed


corollary if_false_lck_simp:
  assumes "\<Turnstile> { conj P (holds_forall_hyper I (lnot_hyper bs)) } [[i \<mapsto> (Cs2 i) | i \<in> I]] { Q }"
    shows "\<Turnstile> { conj P (holds_forall_hyper I (lnot_hyper bs))} [[ i \<mapsto> (if_then_else (bs i) (Cs1 i) (Cs2 i)) | i \<in> I ]] { Q }"
proof -
  let ?Cs' = "\<lambda>i. None"
  from if_false_lck[where Cs'="?Cs'"] assms show ?thesis
    by fastforce
qed


corollary if_sync_lck_simp:
  assumes "\<Turnstile> { conj P (holds_forall_hyper I bs) } [[i \<mapsto> (Cs1 i) | i \<in> I]] { Q }"
    and   "\<Turnstile> { conj P (holds_forall_hyper I (lnot_hyper bs)) } [[i \<mapsto> (Cs2 i) | i \<in> I]] { Q }"
    shows "\<Turnstile> { conj P (low_exp_hyper I bs)} [[ i \<mapsto> (if_then_else (bs i) (Cs1 i) (Cs2 i)) | i \<in> I ]] { Q }"
proof -
  let ?Cs' = "\<lambda>i. None"
  from if_sync_lck[where Cs'="?Cs'"] assms show ?thesis
    by fastforce
qed


corollary if_sync_lck_arb_simp:
    assumes "\<forall>i\<in>I. entails P (\<lambda>S. ((holds_forall (bs i) (S i)))) \<or> entails P (\<lambda>S. ((holds_forall (lnot (bs i)) (S i))))"
    and     "\<Turnstile> { P } [[ i \<mapsto> (pick_branch P bs Cs1 Cs2 i) | i \<in> I]] { Q }"
  shows     "\<Turnstile> { P } [[ i \<mapsto> (if_then_else (bs i) (Cs1 i) (Cs2 i)) | i \<in> I ]] { Q }"
proof -
  let ?Cs' = "\<lambda>i. None"
  from if_sync_lck_arb[where Cs'="?Cs'"] assms show ?thesis
    by fastforce
qed








section\<open>3.4 Relational decomposition of if\<close>

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


lemma set_filter_lnot:
  "S = Set.filter (b \<circ> snd) S \<union> Set.filter (lnot b \<circ> snd) S"
  apply rule
  unfolding lnot_def apply simp_all
   apply (simp add: subsetI)
  by (simp add: Set.filter_def)


lemma split_charact:
  assumes "is_split 0 old_sets new_sets" (* old_sets 0 = new_sets 0 \<union> new_sets 1 *)
      and "sat_assertion vals states (split 0 Q) new_sets"
    shows "sat_assertion vals states Q old_sets"
  using assms
proof (induct arbitrary: vals states rule: split.induct)
  case (7 A)
  then show ?case
    by (meson split_soundness)
next
  case (8 A)
  then show ?case
    by (meson split_soundness)
qed (auto)


fun split_first_set where
  "split_first_set b S 0 = Set.filter (b \<circ> snd) (S 0)"
| "split_first_set b S (Suc 0) = Set.filter (lnot b \<circ> snd) (S 0)"
| "split_first_set b S (Suc (Suc n)) = S (Suc n)"
  
lemma charact_split_first_set:
  shows "is_split 0 (sem_rel [0 \<mapsto> if_then_else b C1 C2] S) (sem_rel [0 \<mapsto> C1, 1 \<mapsto> C2] (split_first_set b S))"
  unfolding is_split_def sem_rel_def apply simp
  apply (rule conjI)
   apply (simp add:  assume_sem if_then_else_def sem_if sem_seq)
  by (metis Suc_lessD diff_Suc_Suc gr0_conv_Suc minus_nat.diff_0 split_first_set.simps(3) zero_less_diff)


lemma needed_for_soundness:
  assumes "interp_assert (split 0 Q) (sem_rel [0 \<mapsto> C1, 1 \<mapsto> C2] (split_first_set b S))"
    shows "interp_assert Q (sem_rel [0 \<mapsto> if_then_else b C1 C2] S)"
  using assms(1)
  apply(auto)
  apply (rule split_charact[rotated])
  using charact_split_first_set apply(simp)
  using charact_split_first_set
  by (metis One_nat_def)

fun split_at_zero where
  "split_at_zero (AConst b) = AConst b"
| "split_at_zero (AComp e1 cmp e2) = AComp e1 cmp e2"
| "split_at_zero (AForallState 0 A) = AAnd (AForallState 0 (split_at_zero A)) (AForallState 1 (split_at_zero A))"
| "split_at_zero (AForallState (Suc n) A) = AForallState (Suc (Suc n)) (split_at_zero A)"
| "split_at_zero (AExistsState 0 A) = AOr (AExistsState 0 (split_at_zero A)) (AExistsState 1 (split_at_zero A))"
| "split_at_zero (AExistsState (Suc n) A) = AExistsState (Suc (Suc n)) (split_at_zero A)"
| "split_at_zero (AForall A) = AForall (split_at_zero A)"
| "split_at_zero (AExists A) = AExists (split_at_zero A)"
| "split_at_zero (AOr A B) = AOr (split_at_zero A) (split_at_zero B)"
| "split_at_zero (AAnd A B) = AAnd (split_at_zero A) (split_at_zero B)"

lemma split_zero_lemma: "split_at_zero P = split 0 P"
proof (induction P)
  case (AForallState x P)
  then show ?case 
  proof (cases x)
    case 0
    with AForallState show ?thesis by auto
  next
    case (Suc nat)
    with AForallState show ?thesis by auto
  qed
next
  case (AExistsState x P)
  then show ?case 
  proof (cases x)
    case 0
    with AExistsState show ?thesis by auto
  next
    case (Suc nat)
    with AExistsState show ?thesis by auto
  qed
qed (auto)


text\<open>IfRelDecomp\<close>
theorem if_relational_decomposition:
  assumes "\<Turnstile> { conj (interp_assert (split_at_zero P)) (conj (\<lambda>S. holds_forall b (S 0)) (\<lambda>S. holds_forall (lnot b) (S 1))) } 
              [[0 \<mapsto> C1, 1 \<mapsto> C2]] 
              {interp_assert (split_at_zero Q)}"
  shows "\<Turnstile> { interp_assert P } [[0 \<mapsto> if_then_else b C1 C2]] {interp_assert Q}"
proof (rule relational_hyper_hoare_tripleI)
  fix S assume asm0: "interp_assert P S"

  let ?S = "split_first_set b S"

  have "conj (interp_assert (split 0 P)) (conj (\<lambda>S. holds_forall b (S 0)) (\<lambda>S. holds_forall (lnot b) (S 1))) ?S"
    unfolding  conj_def apply simp_all
    apply (rule conjI)
     defer
     apply (simp add: holds_forall_def lnot_def)
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
  then have "interp_assert (split 0 Q) (sem_rel [0 \<mapsto> C1, 1 \<mapsto> C2] ?S)"
    using assms(1) unfolding relational_hyper_hoare_triple_def
    by(simp only: split_zero_lemma)
  then show "interp_assert Q (sem_rel [0 \<mapsto> if_then_else b C1 C2] S)"
    using needed_for_soundness by blast
qed









section\<open>3.5 Fixed alignment of loops\<close>

subsection\<open>3.5.1 Fully synchronized lockstep rule for loops\<close>

text\<open>emp_I\<close>
definition hyper_emp where
  "hyper_emp I S \<longleftrightarrow> (\<forall>i \<in> I. (S i) = {})"

lemma least_or_none: "(\<exists>(n::nat). (P n) \<and> (\<forall>m<n. \<not>(P m))) \<or> (\<forall>(n::nat). \<not>(P n))"
  using exists_least_iff by auto


lemma hyper_seq_sem:
  "sem_rel [ i \<mapsto> (Cs2 i) | i \<in> I ] (sem_rel [ i \<mapsto> (Cs1 i) | i \<in> I ] S) = sem_rel [ i \<mapsto> Seq (Cs1 i) (Cs2 i) | i \<in> I ] S"
  unfolding sem_rel_def map_comprehension_def
  apply (rule ext)
     apply simp_all
  using sem_seq by blast


fun sem_lifted_after_n where
"sem_lifted_after_n 0 C S = S" |
"sem_lifted_after_n (Suc n) C S = sem_rel C (sem_lifted_after_n n C S)"

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
      assume "\<exists>xa. x \<in> sem_rel (map_comprehension Cs (\<lambda>i. i \<in> I)) (sem_lifted_after_n xa (map_comprehension Cs (\<lambda>i. i \<in> I)) S) i"
      from this obtain n where "x \<in> sem_rel (map_comprehension Cs (\<lambda>i. i \<in> I)) (sem_lifted_after_n n (map_comprehension Cs (\<lambda>i. i \<in> I)) S) i" by blast
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


lemma while_union: "(sem_rel [ i \<mapsto> While (Cs i)| i \<in> I ] S) 
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
              by (auto simp add:sem_rel_rewrite sem_def)

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
                  hence "x \<in> sem_rel (\<lambda>i. if i \<in> I then Some (Cs i) else None) (sem_lifted_after_n n (\<lambda>i. if i \<in> I then Some (Cs i) else None) S) i" by auto
                  from this \<open>i \<in> I\<close>
                  have "x \<in> {x. \<exists>\<sigma>' \<sigma> l. x = (l, \<sigma>') \<and> (l, \<sigma>) \<in> sem_lifted_after_n n (\<lambda>i. if i \<in> I then Some (Cs i) else None) S i \<and> \<langle>Cs i, \<sigma>\<rangle> \<rightarrow> \<sigma>'}"
                    using sem_rel_def sem_def by (smt (verit, ccfv_threshold) map_comprehension_def mem_Collect_eq sem_rel_rewrite) 
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
                hence "x \<in> sem_rel (\<lambda>i. if i \<in> I then Some (Cs i) else None) (sem_lifted_after_n n (\<lambda>i. if i \<in> I then Some (Cs i) else None) S) i" by auto
                from this Suc show ?case using \<open>i\<notin>I\<close> by (auto simp add:sem_rel_def)
              qed
            qed
          qed
          thus "x \<in> (if i \<in> I then sem (While (Cs i)) (S i) else S i)" using \<open>i \<notin> I\<close> by (auto)
        qed
      qed
    qed
  qed  
  show ?thesis by (simp add:fact sem_rel_rewrite)
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
      by (simp add: \<open>i \<notin> I\<close> sem_rel_rewrite)
  qed
qed


text\<open>WhileSyncLck\<close>
theorem while_sync_lck:
    assumes "\<Turnstile> { conj Iv (holds_forall_hyper I bs) } [[i \<mapsto> (Cs i) | i \<in> I]] { conj Iv (low_exp_hyper I bs)}"
    shows   "\<Turnstile> { conj Iv (low_exp_hyper I bs)} [[ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ]] { conj (disj Iv (hyper_emp I)) (holds_forall_hyper I (lnot_hyper bs))}"
proof -
  from assms[unfolded relational_hyper_hoare_triple_def] have "\<forall>S. conj Iv (holds_forall_hyper I bs) S \<longrightarrow>
      conj Iv (low_exp_hyper I bs) (sem_rel [i \<mapsto> (Cs i) | i \<in> I] S) " by auto
  
  moreover have "\<forall>S. conj Iv (holds_forall_hyper I bs) S \<longrightarrow>
      conj Iv (holds_forall_hyper I bs) (sem_rel [i \<mapsto> Assume (bs i) | i \<in> I] S)" 
  proof
    fix S
    show "conj Iv (holds_forall_hyper I bs) S \<longrightarrow>
      conj Iv (holds_forall_hyper I bs) (sem_rel [i \<mapsto> Assume (bs i) | i \<in> I] S)"
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
      thus "conj Iv (holds_forall_hyper I bs) (sem_rel [i \<mapsto> Assume (bs i) | i \<in> I] S)" by (simp add: H sem_rel_rewrite)
    qed
  qed

  ultimately have "\<forall>S. conj Iv (holds_forall_hyper I bs) S \<longrightarrow>
        conj Iv (low_exp_hyper I bs) (sem_rel [i \<mapsto> (Cs i) | i \<in> I] (sem_rel [i \<mapsto> Assume (bs i) | i \<in> I] S))"  by blast

  hence step_holds: "\<forall>S. conj Iv (holds_forall_hyper I bs) S \<longrightarrow>
      conj Iv (low_exp_hyper I bs) (sem_rel [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)" using hyper_seq_sem
  proof -
    show ?thesis
      by (metis (no_types) \<open>\<forall>S. Logic.conj Iv (holds_forall_hyper I bs) S \<longrightarrow> Logic.conj Iv (low_exp_hyper I bs) (sem_rel (map_comprehension Cs (\<lambda>i. i \<in> I)) (sem_rel (map_comprehension (\<lambda>i. Assume (bs i)) (\<lambda>i. i \<in> I)) S))\<close> hyper_seq_sem)
  qed


  have while_is_union: "\<forall>S. (sem_rel [ i \<mapsto> While (Assume (bs i);; Cs i)| i \<in> I ] S) 
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
              with iv_holds conj_def step_holds have "conj Iv (low_exp_hyper I bs) (sem_rel (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) (sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S))"
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
              hence "conj (hyper_emp I) (low_exp_hyper I bs) (sem_rel (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) ?S')"
                by (simp add: H sem_rel_rewrite)
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
            hence "conj (hyper_emp I) (low_exp_hyper I bs) (sem_rel (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) ?S')"
              by (simp add: H sem_rel_rewrite)
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
                    by (auto simp add:holds_forall_hyper_def lnot_hyper_def snd_def sem_rel_rewrite sem_def)
                next
                  show "sem_lifted_after_n (Suc 0) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S =
                      (\<lambda>i. if i \<in> I then {} else sem_lifted_after_n (Suc 0) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i)"
                    apply(auto simp add:sem_rel_rewrite)
                  proof
                    fix i
                    have "i\<in>I \<or> i\<notin>I" by auto
                    thus "(if i \<in> I then sem (Assume (bs i) ;; Cs i) (S i) else S i) =
                      (if i \<in> I then {} else sem_lifted_after_n (Suc 0) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i)"
                    proof
                      assume "i \<in> I"
                      with asm_0 show "(if i \<in> I then sem (Assume (bs i) ;; Cs i) (S i) else S i) =
                      (if i \<in> I then {} else sem_lifted_after_n (Suc 0) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i)"
                        by (auto simp add:holds_forall_hyper_def lnot_hyper_def snd_def sem_rel_rewrite sem_def)
                    next 
                      assume "i\<notin>I"
                      with asm_0 show "(if i \<in> I then sem (Assume (bs i) ;; Cs i) (S i) else S i) =
                                              (if i \<in> I then {} else sem_lifted_after_n (Suc 0) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i)"
                        by (auto simp add:holds_forall_hyper_def lnot_hyper_def snd_def sem_rel_rewrite sem_def)
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
                      apply(auto simp add:sem_rel_rewrite)
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
                          by (auto simp add:sem_rel_rewrite)
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
                    thus " sem_rel (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I))
          (\<lambda>i. if i \<in> I then {} else sem_lifted_after_n (Suc m'') (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i) i =
         (if i \<in> I then {} else sem_lifted_after_n (Suc (Suc m'')) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i)"
                    proof
                      assume "i \<in> I"
                      thus " sem_rel (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I))
          (\<lambda>i. if i \<in> I then {} else sem_lifted_after_n (Suc m'') (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i) i =
         (if i \<in> I then {} else sem_lifted_after_n (Suc (Suc m'')) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i)"
                        by (auto simp add:sem_rel_rewrite sem_def)
                      next 
                        assume "i\<notin>I"
                        thus "sem_rel (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I))
          (\<lambda>i. if i \<in> I then {} else sem_lifted_after_n (Suc m'') (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i) i =
         (if i \<in> I then {} else sem_lifted_after_n (Suc (Suc m'')) (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i)"
                          by (auto simp add:sem_rel_rewrite sem_def)
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
    \<longrightarrow> sem_rel [ i \<mapsto> Assume (lnot (bs i)) | i \<in> I ] (pointwise_Union {i::nat | i. i \<le> n} (\<lambda>n. (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)))
        = (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))" 
  proof
    fix S
    show "conj Iv (low_exp_hyper I bs) S \<longrightarrow> 
        (\<forall>n. (holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S) 
        \<and> (\<forall>m<n. (holds_forall_hyper I bs) (sem_lifted_after_n m [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))
    \<longrightarrow> sem_rel [ i \<mapsto> Assume (lnot (bs i)) | i \<in> I ] (pointwise_Union {i::nat | i. i \<le> n} (\<lambda>n. (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)))
        = (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))"
    proof
      assume "conj Iv (low_exp_hyper I bs) S"
      show " (\<forall>n. (holds_forall_hyper I (lnot_hyper bs)) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S) 
        \<and> (\<forall>m<n. (holds_forall_hyper I bs) (sem_lifted_after_n m [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))
    \<longrightarrow> sem_rel [ i \<mapsto> Assume (lnot (bs i)) | i \<in> I ] (pointwise_Union {i::nat | i. i \<le> n} (\<lambda>n. (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)))
        = (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))"
      proof
        fix n
        show "holds_forall_hyper I (lnot_hyper bs) (sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S) \<and>
         (\<forall>m<n. holds_forall_hyper I bs (sem_lifted_after_n m (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)) \<longrightarrow>
         sem_rel (map_comprehension (\<lambda>i. Assume (lnot (bs i))) (\<lambda>i. i \<in> I))
          (pointwise_Union {i |i. i \<le> n} (\<lambda>n. sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)) =
         sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S"
        proof
          assume asm: "holds_forall_hyper I (lnot_hyper bs) (sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S) \<and>
    (\<forall>m<n. holds_forall_hyper I bs (sem_lifted_after_n m (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S))"
          show "sem_rel (map_comprehension (\<lambda>i. Assume (lnot (bs i))) (\<lambda>i. i \<in> I))
                (pointwise_Union {i |i. i \<le> n} (\<lambda>n. sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)) =
                sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S"
          proof
            fix i
            from asm show "sem_rel (map_comprehension (\<lambda>i. Assume (lnot (bs i))) (\<lambda>i. i \<in> I))
          (pointwise_Union {i |i. i \<le> n} (\<lambda>n. sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)) i =
         sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S i"
              apply(auto simp add:sem_rel_rewrite sem_def pointwise_Union_def lnot_def holds_forall_hyper_def lnot_hyper_def snd_def)
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
                with step_holds have "Logic.conj Iv (low_exp_hyper I bs) (sem_rel (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) (sem_lifted_after_n m (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S))" by auto
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
            with step_holds have "Logic.conj Iv (low_exp_hyper I bs) (sem_rel (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I))  (sem_lifted_after_n n' (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S))" by auto
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
       (sem_rel [ i \<mapsto> Assume (lnot (bs i)) | i \<in> I ] (sem_rel [ i \<mapsto> While (Assume (bs i);; Cs i)| i \<in> I ] S))" 
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
         (sem_rel [ i \<mapsto> Assume (lnot (bs i)) | i \<in> I ]  (pointwise_Union (UNIV :: nat set) (\<lambda>n. (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))))
          = (\<lambda>i. (if i\<in>I then {} else S i))" 
  proof
    fix S
    show "Logic.conj Iv (low_exp_hyper I bs) S \<longrightarrow>
         (\<forall>n. holds_forall_hyper I bs (sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)) \<longrightarrow>
         sem_rel (map_comprehension (\<lambda>i. Assume (lnot (bs i))) (\<lambda>i. i \<in> I))
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
          from asm2 show " sem_rel (map_comprehension (\<lambda>i. Assume (lnot (bs i))) (\<lambda>i. i \<in> I))
          (pointwise_Union UNIV (\<lambda>n. sem_lifted_after_n n (map_comprehension (\<lambda>i. Assume (bs i) ;; Cs i) (\<lambda>i. i \<in> I)) S)) i =
         (if i \<in> I then {} else S i)"
            apply(auto simp add:sem_rel_rewrite sem_def pointwise_Union_def lnot_def holds_forall_hyper_def snd_def)
              apply(fastforce)
            by(auto simp add:outsideI_preserved)
        qed
      qed
    qed
  qed

  have fact9: "\<forall>S. conj Iv (low_exp_hyper I bs) S \<longrightarrow>
        (\<forall>n. (holds_forall_hyper I bs) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)) \<longrightarrow> 
        conj (hyper_emp I) (holds_forall_hyper I (lnot_hyper bs))
         (sem_rel [ i \<mapsto> Assume (lnot (bs i)) | i \<in> I ]  (pointwise_Union (UNIV :: nat set) (\<lambda>n. (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))))"  
  proof
    fix S
    show "conj Iv (low_exp_hyper I bs) S \<longrightarrow> (\<forall>n. (holds_forall_hyper I bs) (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S)) \<longrightarrow> 
        conj (hyper_emp I) (holds_forall_hyper I (lnot_hyper bs))
         (sem_rel [ i \<mapsto> Assume (lnot (bs i)) | i \<in> I ]  (pointwise_Union (UNIV :: nat set) (\<lambda>n. (sem_lifted_after_n n [i \<mapsto> Assume (bs i);;(Cs i) | i \<in> I] S))))" (is "?P \<longrightarrow> (?R \<longrightarrow>?Q)")
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
           (sem_rel [ i \<mapsto> Assume (lnot (bs i)) | i \<in> I ] (sem_rel [ i \<mapsto> While (Assume (bs i);; Cs i)| i \<in> I ] S))"  
    by (simp add: fact9 while_is_union)

  have "\<forall>S. conj Iv (low_exp_hyper I bs) S \<longrightarrow>
      conj (disj Iv (hyper_emp I)) (holds_forall_hyper I (lnot_hyper bs))
       (sem_rel [ i \<mapsto> Assume (lnot (bs i)) | i \<in> I ] (sem_rel [ i \<mapsto> While (Assume (bs i);; Cs i)| i \<in> I ] S))" 
    by (metis (mono_tags, lifting) conj_def disj_def exists_leastn_or_not if_n_then_IV_and_holds_notbs if_exists_not_then_EMP_and_holds_notbs)

  hence "\<forall>S. conj Iv (low_exp_hyper I bs) S \<longrightarrow>
      conj (disj Iv (hyper_emp I)) (holds_forall_hyper I (lnot_hyper bs))
       (sem_rel [ i \<mapsto> While (Assume (bs i);; Cs i);; Assume (lnot (bs i)) | i \<in> I ] S)" by (auto simp add:hyper_seq_sem)

  thus ?thesis 
    by (simp add: relational_hyper_hoare_tripleI while_cond_def)
qed



subsection\<open>3.5.2 Variable fixed alignment lockstep rule for loops\<close>

fun repeat_with_if where
"repeat_with_if 0 b C = Skip" |
"repeat_with_if (Suc r) b C = Seq (if_then_else_skip b C) (repeat_with_if r b C)"


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
          apply(auto simp add:if_then_else_skip_def if_then_else_def)
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
          apply(auto simp add:if_then_else_skip_def if_then_else_def)
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
        apply(auto simp add:if_then_else_skip_def if_then_else_def)
        by (metis SemAssume SemIf2 SemSeq SemSkip lnot_def)
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
      hence "\<langle>if_then_else_skip b C ;; repeat_with_if n b C, \<sigma>\<rangle> \<rightarrow> \<sigma>'" by auto
      from this obtain \<phi> where "\<langle>if_then_else_skip b C, \<sigma>\<rangle> \<rightarrow> \<phi>" and "\<langle>repeat_with_if n b C, \<phi>\<rangle> \<rightarrow> \<sigma>'" by auto
      from \<open>\<langle>if_then_else_skip b C, \<sigma>\<rangle> \<rightarrow> \<phi>\<close> have \<phi>_cond:"\<phi> = \<sigma> \<or> (b \<sigma> \<and> \<langle>C, \<sigma>\<rangle> \<rightarrow> \<phi>)" unfolding if_then_else_skip_def if_then_else_def by auto
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


lemma while_unfolded: "(\<forall>i\<in>I. (rf i) > 0) \<Longrightarrow> sem_rel [ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ] S = (sem_rel [ i \<mapsto> while_cond (bs i) (repeat_with_if (rf i) (bs i) (Cs i)) | i \<in> I ] S)"
  apply(simp only: sem_rel_rewrite)
  apply(rule ext)
  apply(simp add: outsideI_preserved)
  apply(intro impI)
  using while_unfolded_sem by blast


text\<open>WhileFixedLck\<close>
theorem while_fixed_lck:
  assumes "\<Turnstile> { conj Iv (holds_forall_hyper I bs)} [[i \<mapsto> repeat_with_if (rf i) (bs i) (Cs i) | i \<in> I]] { conj Iv (low_exp_hyper I bs)}" 
      and "(\<forall>i\<in>I. (rf i) > 0)"
    shows "\<Turnstile> { conj Iv (low_exp_hyper I bs)} [[ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ]] { conj (disj Iv (hyper_emp I)) (holds_forall_hyper I (lnot_hyper bs))}"
proof -
  from assms(1) while_sync_lck have "\<Turnstile> { conj Iv (low_exp_hyper I bs)} [[ i \<mapsto> (while_cond (bs i) (repeat_with_if (rf i) (bs i) (Cs i))) | i \<in> I ]] { conj (disj Iv (hyper_emp I)) (holds_forall_hyper I (lnot_hyper bs))}" by auto
  with assms(2) show ?thesis unfolding relational_hyper_hoare_triple_def using while_unfolded 
    by (metis (mono_tags, lifting))
qed








section\<open>3.6 Nonfixed alignment of loops\<close>


subsection\<open>Upward closedness\<close>
definition hyper_set_le where
  "hyper_set_le I S S' \<longleftrightarrow> (\<forall>i\<in>I. S i \<subseteq> S' i) \<and> (\<forall>i. i \<notin> I \<longrightarrow> S i = S' i)"

lemma hyper_set_leI:
  assumes "\<And>i. i \<in> I \<Longrightarrow> S i \<subseteq> S' i"
      and "\<And>i. i \<notin> I \<Longrightarrow> S i = S' i"
    shows "hyper_set_le I S S'"
  by (simp add: assms(1) assms(2) hyper_set_le_def)

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






subsection\<open>Progress side-conditions\<close>

definition disj_I where
"disj_I I Ps S \<longleftrightarrow> (\<exists>i\<in>I. (Ps i) S)"

abbreviation progress_side_condition1 where
"progress_side_condition1 Iv I bs V \<equiv> \<forall>n. entails (Iv n) (disj (disj_I (Pow I - {{}}) (\<lambda>J. V J)) (holds_forall_hyper I (lnot_hyper bs)))"

abbreviation progress_side_condition2 where
"progress_side_condition2 Iv I bs V \<equiv> \<forall>n::nat. \<forall>i\<in>I. \<exists>n'\<ge>n. (entails (Iv n') (disj (\<lambda>S. (holds_forall (lnot (bs i)) (S i))) (disj_I ({J . J \<in> Pow I \<and> i \<in> J}) (\<lambda>J. V J))))" 



lemma progress_side_condition1_exists_out:
  assumes "I \<noteq> {}"
      and "progress_side_condition1 Iv I bs V"
    shows "\<forall>n. \<forall>S. \<exists>J\<in>(Pow I - {{}}). (Iv n) S \<longrightarrow> ((disj (V J) (holds_forall_hyper I (lnot_hyper bs))) S)"
  using assms unfolding entails_def disj_I_def
  by (smt (verit, ccfv_threshold) Diff_empty Diff_insert0 Pow_not_empty Pow_singleton_iff disj_def empty_Collect_eq insert_Diff mem_Collect_eq set_diff_eq)


subsection\<open>The nonfixed alignment rule\<close>

lemma least_one_exists:
  assumes "\<exists>n::nat. P n"
  shows "\<exists>n::nat. P n \<and> (\<forall>n'::nat < n. \<not> (P n'))"
  using assms 
  using least_or_none by auto


definition priority_picker where
  "priority_picker JS p n S =
     (if \<exists>J\<in>JS n S. p \<in> J
      then (SOME J. J \<in> JS n S \<and> p \<in> J)
      else (SOME J. J \<in> JS n S))"

definition qth_program :: "nat set \<Rightarrow> nat \<Rightarrow> nat" where
  "qth_program I q  = 
     (THE i. i \<in> I \<and> card {j \<in> I. j < i} = q)"

definition next_len :: "nat set \<Rightarrow> nat \<Rightarrow> nat" where
  "next_len I l =
     (if finite I then min (Suc l) (card I) else Suc l)"

fun priority_JS_based_execution_aux where
  "priority_JS_based_execution_aux bs Cs S JS I 0 = (S, 1, 0)" |
  "priority_JS_based_execution_aux bs Cs S JS I (Suc n) =
     (let (Sn,l,q) = priority_JS_based_execution_aux bs Cs S JS I n;
          p = qth_program I q;
          J = priority_picker JS p n Sn;
          Sn' = sem_rel [i \<mapsto> if_then_else_skip (bs i) (Cs i) | i \<in> J] Sn
      in
        if p \<in> J \<or> (holds_forall (lnot (bs p)) (Sn p)) then
          if Suc q < l then (Sn', l, Suc q)
          else (Sn', next_len I l, 0)
        else
          (Sn', l, q))"

definition priority_JS_based_execution where
  "priority_JS_based_execution bs Cs S JS I n =
     fst (priority_JS_based_execution_aux bs Cs S JS I n)"

abbreviation current_q where
  "current_q E \<equiv> snd (snd (E))"

abbreviation current_l where
  "current_l E \<equiv> fst (snd (E))"

abbreviation valid_qs where
  "valid_qs I \<equiv> (if finite I then {0..<card I} else UNIV::nat set)"


lemma priority_picker_inJS:
  assumes "JS n S \<noteq> {}"
  shows "priority_picker JS p n S \<in> JS n S"
  apply(simp add: priority_picker_def)
proof (intro conjI impI)
  assume ex: "\<exists>J\<in>JS n S. p \<in> J"
  then have "\<exists>J. J \<in> JS n S \<and> p \<in> J"
    by blast
  show "(SOME J. J \<in> JS n S \<and> p \<in> J) \<in> JS n S"
    using someI_ex[where ?P="\<lambda>x. x \<in> JS n S \<and> p \<in> x "] ex
    by(auto)
next
  assume no: "\<forall>x\<in>JS n S. p \<notin> x"
  from assms have "\<exists>J. J \<in> JS n S"
    by blast
  then show "(SOME J. J \<in> JS n S) \<in> JS n S"
    by (rule someI_ex)
qed


lemma priority_picker_contains_p:
  assumes "\<exists>J\<in>JS n S. p \<in> J"
  shows "p \<in> priority_picker JS p n S"
  apply(simp add: priority_picker_def)
proof (intro conjI impI)
  from assms have ex:"\<exists>J. J \<in> JS n S \<and> p \<in> J"
    by blast
  show "p \<in> (SOME J. J \<in> JS n S \<and> p \<in> J)"
    using someI_ex[where ?P="\<lambda>x. x \<in> JS n S \<and> p \<in> x "] ex
    by(auto)
next 
  assume "\<forall>x\<in>JS n S. p \<notin> x"
  with assms show "p \<in> (SOME J. J \<in> JS n S)" by auto
qed



lemma priority_JS_based_execution_step:
  shows "\<exists>J. priority_JS_based_execution bs Cs S JS I (Suc n) = sem_rel [i \<mapsto> if_then_else_skip (bs i) (Cs i) | i \<in> J]
         (priority_JS_based_execution bs Cs S JS I n)"
proof -
  obtain Sn l q where
    Haux: "priority_JS_based_execution_aux bs Cs S JS I n = (Sn,l,q)"
    by (cases "priority_JS_based_execution_aux bs Cs S JS I n")
  let ?p = "qth_program I q"
  let ?J = "priority_picker JS ?p n Sn"
  have "priority_JS_based_execution bs Cs S JS I (Suc n) =
        sem_rel [i \<mapsto> if_then_else_skip (bs i) (Cs i) | i \<in> ?J]
          (priority_JS_based_execution bs Cs S JS I n)"
    unfolding priority_JS_based_execution_def
    using Haux
    by (simp add: Let_def)
  thus ?thesis
    by blast
qed


lemma priority_picker_in_or_none:
  assumes "JS n S \<noteq> {}"
  shows
    "priority_picker JS p n S \<in> JS n S \<and>
     (p \<in> priority_picker JS p n S \<or> (\<forall>J\<in>JS n S. p \<notin> J))"
  using assms
  unfolding priority_picker_def
  by (metis (no_types, lifting) someI_ex some_elem_nonempty)

lemma priority_JS_based_execution_step_strong:
  assumes nz: "\<forall>n S. JS n S \<noteq> {}"
  shows "\<exists>J. priority_JS_based_execution bs Cs S JS I (Suc n) =
           sem_rel [i \<mapsto> if_then_else_skip (bs i) (Cs i) | i \<in> J]
             (priority_JS_based_execution bs Cs S JS I n)
         \<and> J \<in> JS n (priority_JS_based_execution bs Cs S JS I n)
         \<and> (qth_program I (current_q (priority_JS_based_execution_aux bs Cs S JS I n)) \<in> J
            \<or> (\<forall>J\<in>JS n (priority_JS_based_execution bs Cs S JS I n).
                  qth_program I (current_q (priority_JS_based_execution_aux bs Cs S JS I n)) \<notin> J))"
proof -
  obtain Sn l q where Haux:
    "priority_JS_based_execution_aux bs Cs S JS I n = (Sn,l,q)"
    by (cases "priority_JS_based_execution_aux bs Cs S JS I n")

  let ?p = "qth_program I (current_q (priority_JS_based_execution_aux bs Cs S JS I n))"
  let ?J = "priority_picker JS ?p n Sn"

  have Hq: "current_q (priority_JS_based_execution_aux bs Cs S JS I n) = q"
    using Haux
    by (simp)

  have Hstate: "priority_JS_based_execution bs Cs S JS I n = Sn"
    using Haux
    unfolding priority_JS_based_execution_def
    by simp

  have Hpick:
    "?J \<in> JS n Sn \<and> (?p \<in> ?J \<or> (\<forall>J\<in>JS n Sn. ?p \<notin> J))"
    using nz
    by (simp add: priority_picker_in_or_none)

  have Hstep:
    "priority_JS_based_execution bs Cs S JS I (Suc n) =
      sem_rel [i \<mapsto> if_then_else_skip (bs i) (Cs i) | i \<in> ?J]
        (priority_JS_based_execution bs Cs S JS I n)"
    using Haux
    unfolding priority_JS_based_execution_def
    by (simp add: Let_def Hq)

  from Hstep Hpick Hstate
  have "priority_JS_based_execution bs Cs S JS I (Suc n) =
          sem_rel [i \<mapsto> if_then_else_skip (bs i) (Cs i) | i \<in> ?J]
            (priority_JS_based_execution bs Cs S JS I n)
        \<and> ?J \<in> JS n (priority_JS_based_execution bs Cs S JS I n)
        \<and> (qth_program I (current_q (priority_JS_based_execution_aux bs Cs S JS I n)) \<in> ?J
           \<or> (\<forall>J\<in>JS n (priority_JS_based_execution bs Cs S JS I n).
                 qth_program I (current_q (priority_JS_based_execution_aux bs Cs S JS I n)) \<notin> J))"
    by simp
  then show ?thesis
    by blast
qed


lemma priority_JS_based_execution_base:
  shows "priority_JS_based_execution bs Cs S JS I 0 = S"
  by(auto simp add:priority_JS_based_execution_def)

fun sem_lifted_after_n_steps where
"sem_lifted_after_n_steps bs Cs S I 0 = S" |
"sem_lifted_after_n_steps bs Cs S I (Suc n) = sem_rel [i \<mapsto> if_then_else_skip (bs i) (Cs i) | i \<in> I] (sem_lifted_after_n_steps bs Cs S I n)"




lemma state_preservation:
  assumes "\<not>(\<exists>n''\<ge>n. n'' < n' \<and> (\<exists>J \<in> JS n'' (priority_JS_based_execution bs Cs S JS I n''). i \<in> J \<and>
        priority_JS_based_execution bs Cs S JS I (Suc n'') = sem_rel [i \<mapsto> if_then_else_skip (bs i) (Cs i) | i \<in> J] (priority_JS_based_execution bs Cs S JS I n'')))"
    and "n' \<ge> n"
    and  JS_nonempty: "\<And>n S.((JS n S) \<noteq> {})"
  shows "\<forall>n''. n \<le> n'' \<and> n''\<le>n' \<longrightarrow> (priority_JS_based_execution bs Cs S JS I n'') i = (priority_JS_based_execution bs Cs S JS I n) i"
proof(intro allI ballI impI, elim conjE)
  fix n''
  assume asm1:"n \<le> n''"
  assume asm2:"n'' \<le> n'"
  show "(priority_JS_based_execution bs Cs S JS I n'') i = (priority_JS_based_execution bs Cs S JS I n) i"
  using assms(1) assms(2) asm1 asm2
  proof (induction n'')
    case 0
    hence "n = 0" by auto
    then show ?case by auto
  next
    case (Suc m)
    hence H0:"\<not> (\<exists>n''\<ge>n.
         n'' < Suc m \<and>
         (\<exists>J\<in>JS n'' (priority_JS_based_execution bs Cs S JS I n'').
             i \<in> J \<and>
             priority_JS_based_execution bs Cs S JS I (Suc n'') =
             sem_rel (map_comprehension (\<lambda>i. if_then_else_skip (bs i) (Cs i)) (\<lambda>i. i \<in> J)) (priority_JS_based_execution bs Cs S JS I n'')))" by auto
    have "n = Suc m \<or> n\<noteq>Suc m" by auto
    then show ?case 
    proof
      assume "n = Suc m"
      then show ?case by auto
    next
      assume "n \<noteq> Suc m"
      with Suc have "n \<le> m" by auto
      with Suc have H:"priority_JS_based_execution bs Cs S JS I m i = priority_JS_based_execution bs Cs S JS I n i" by auto
      from priority_JS_based_execution_step_strong JS_nonempty obtain J' where eq:"priority_JS_based_execution bs Cs S JS I (Suc m) = sem_rel [i \<mapsto> if_then_else_skip (bs i) (Cs i) | i \<in> J'] (priority_JS_based_execution bs Cs S JS I m)"
                                                                           and jinJS:"J' \<in> JS m (priority_JS_based_execution bs Cs S JS I m)" by blast
      show ?case
      proof (rule ccontr)
        assume "priority_JS_based_execution bs Cs S JS I (Suc m) i \<noteq> priority_JS_based_execution bs Cs S JS I n i"
        hence "i\<in>J'"
          apply(simp only:eq)
          apply(auto simp add:sem_rel_def map_comprehension_def)
          using H by auto
        from \<open>i\<in>J'\<close> eq jinJS H0 \<open>n \<le> m\<close> show "False" by blast
      qed
    qed
  qed
qed


lemma qth_program_surj:
  "\<forall>i::nat\<in>I. \<exists>k\<in>valid_qs I. qth_program I k = i"
proof
  fix i::nat
  assume iI: "i \<in> I"
  let ?k = "card {j \<in> I. j < i}"

  have k_valid: "?k \<in> valid_qs I"
  proof (simp, intro impI)
    assume fin: "finite I"
    have "{j \<in> I. j < i} \<subset> I"
      using iI by auto
    moreover have "finite {j \<in> I. j < i}"
      using fin by auto
    ultimately have "card {j \<in> I. j < i} < card I"
      using fin psubset_card_mono by blast
    thus "?k < card I"
      by simp
  qed

  have qth_eq: "qth_program I ?k = i"
  proof (unfold qth_program_def, rule the_equality)
    show "i \<in> I \<and> card {j \<in> I. j < i} = ?k"
      using iI by simp
  next
    fix x
    assume hx: "x \<in> I \<and> card {j \<in> I. j < x} = ?k"
    then have xI: "x \<in> I"
      by simp
    have card_eq: "card {j \<in> I. j < x} = card {j \<in> I. j < i}"
      using hx by simp
    show "x = i"
    proof (cases x i rule: linorder_cases)
      case less
      then have "{j \<in> I. j < x} \<subset> {j \<in> I. j < i}"
        using xI iI by auto
      moreover have "finite {j \<in> I. j < i}"
        by simp
      ultimately have "card {j \<in> I. j < x} < card {j \<in> I. j < i}"
        using psubset_card_mono by blast
      with card_eq show ?thesis
        by simp
    next
      case equal
      then show ?thesis
        by simp
    next
      case greater
      then have "{j \<in> I. j < i} \<subset> {j \<in> I. j < x}"
        using xI iI by auto
      moreover have "finite {j \<in> I. j < x}"
        by simp
      ultimately have "card {j \<in> I. j < i} < card {j \<in> I. j < x}"
        using psubset_card_mono by blast
      with card_eq show ?thesis
        by simp
    qed
  qed

  show "\<exists>k\<in>valid_qs I. qth_program I k = i"
    using k_valid qth_eq by blast
qed



lemma qs_to_progs:
  assumes "\<forall>i\<in>valid_qs I. \<forall>n. holds_forall_hyper I (lnot_hyper bs) (priority_JS_based_execution bs Cs S JS I n) \<or> (\<exists>n'\<ge>n. current_q (priority_JS_based_execution_aux bs Cs S JS I n') = i)"
  shows "\<forall>i \<in> I. \<forall>n. holds_forall_hyper I (lnot_hyper bs) (priority_JS_based_execution bs Cs S JS I n) \<or> (\<exists>n'\<ge>n. (qth_program I (current_q (priority_JS_based_execution_aux bs Cs S JS I n'))) = i)"
proof (intro ballI allI)
  fix i n
  assume iI: "i \<in> I"
  from qth_program_surj iI obtain k where
    kvalid: "k \<in> valid_qs I"
    and ki: "qth_program I k = i"
    by blast
  from assms kvalid have
    "holds_forall_hyper I (lnot_hyper bs) (priority_JS_based_execution bs Cs S JS I n) \<or>
     (\<exists>n'\<ge>n. current_q (priority_JS_based_execution_aux bs Cs S JS I n') = k)"
    by blast
  then show
    "holds_forall_hyper I (lnot_hyper bs) (priority_JS_based_execution bs Cs S JS I n) \<or>
     (\<exists>n'\<ge>n. qth_program I (current_q (priority_JS_based_execution_aux bs Cs S JS I n')) = i)"
  proof
    assume
      "holds_forall_hyper I (lnot_hyper bs) (priority_JS_based_execution bs Cs S JS I n)"
    then show ?thesis
      by blast
  next
    assume "\<exists>n'\<ge>n. current_q (priority_JS_based_execution_aux bs Cs S JS I n') = k"
    then obtain n' where
      nn': "n' \<ge> n"
      and qeq: "current_q (priority_JS_based_execution_aux bs Cs S JS I n') = k"
      by blast
    have "qth_program I (current_q (priority_JS_based_execution_aux bs Cs S JS I n')) = i"
      using qeq ki by simp
    then show ?thesis
      using nn' by blast
  qed
qed


lemma l_belonging_lemma:
  assumes "I \<noteq> {}"
  shows "((current_l (priority_JS_based_execution_aux bs Cs S JS I n))-1) \<in> valid_qs I"
proof (induction n)
  case 0
  then show ?case using assms
    by(auto)
next
  case (Suc n)
  obtain Sn l q where
      Haux: "priority_JS_based_execution_aux bs Cs S JS I n = (Sn,l,q)"
      by (cases "priority_JS_based_execution_aux bs Cs S JS I n")
  let ?p = "qth_program I q"
  have eq:"q = current_q (priority_JS_based_execution_aux bs Cs S JS I n)"
    by(auto simp add:Haux)
  have eq2:"l = current_l (priority_JS_based_execution_aux bs Cs S JS I n)"
    by(auto simp add:Haux)
  from Suc have lin:"l- 1 \<in> valid_qs I" by (auto simp add:eq2)
  then show ?case 
    using lin
    by(auto simp add:Haux Let_def next_len_def)
qed

lemma q_l_inequality_lemma:
  assumes "I \<noteq> {}"
  shows "current_q (priority_JS_based_execution_aux bs Cs S JS I n) < current_l (priority_JS_based_execution_aux bs Cs S JS I n)"
proof (induction n)
  case 0
  then show ?case
    by(auto)
next
  case (Suc n)
  obtain Sn l q where
      Haux: "priority_JS_based_execution_aux bs Cs S JS I n = (Sn,l,q)"
      by (cases "priority_JS_based_execution_aux bs Cs S JS I n")
  let ?p = "qth_program I q"
  have eq:"q = current_q (priority_JS_based_execution_aux bs Cs S JS I n)"
    by(auto simp add:Haux)
  have eq2:"l = current_l (priority_JS_based_execution_aux bs Cs S JS I n)"
    by(auto simp add:Haux)
  from Suc have ineq:"q < l"
    by(auto simp add:eq eq2)
  show ?case 
    apply(auto simp add:Haux Let_def next_len_def)
    using assms
    by(auto simp add:ineq)
qed



lemma q_belonging_lemma:
  assumes "I \<noteq> {}"
  shows "(current_q (priority_JS_based_execution_aux bs Cs S JS I n)) \<in> valid_qs I"
proof (induction n)
  case 0
  then show ?case 
    using assms by(auto)
next
  case (Suc n)
  obtain Sn l q where
      Haux: "priority_JS_based_execution_aux bs Cs S JS I n = (Sn,l,q)"
      by (cases "priority_JS_based_execution_aux bs Cs S JS I n")
  let ?p = "qth_program I q"
  have eq:"q = current_q (priority_JS_based_execution_aux bs Cs S JS I n)"
    by(auto simp add:Haux)
  have eq2:"l = current_l (priority_JS_based_execution_aux bs Cs S JS I n)"
    by(auto simp add:Haux)
  have fnl:"finite I \<longrightarrow> l \<le> card I" using l_belonging_lemma[of I bs Cs S JS n] using assms
    by(auto simp add: eq2[symmetric] if_splits)
  show ?case 
    using assms fnl
    apply(auto simp add:Haux Let_def)
    using assms apply(auto)
    by (simp add: dual_order.strict_trans1 eq eq2 q_l_inequality_lemma assms)
qed


lemma l_gr_0: 
  assumes "I \<noteq> {}"
  shows "current_l (priority_JS_based_execution_aux bs Cs S JS I n) > 0"
proof (induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  obtain Sn l q where
      Haux: "priority_JS_based_execution_aux bs Cs S JS I n = (Sn,l,q)"
      by (cases "priority_JS_based_execution_aux bs Cs S JS I n")
  let ?p = "qth_program I q"
  have eq:"q = current_q (priority_JS_based_execution_aux bs Cs S JS I n)"
    by(auto simp add:Haux)
  have eq2:"l = current_l (priority_JS_based_execution_aux bs Cs S JS I n)"
    by(auto simp add:Haux)
  from Suc have leq:"0 < l"
    by(auto simp add:eq2)
  show ?case 
    apply(auto simp add:Haux Let_def next_len_def)
    using assms leq
    by(auto)
qed


lemma l_q_preservation:
  assumes "(\<forall>n''. n \<le> n'' \<and> n''< n'  
  \<longrightarrow> \<not>(holds_forall (lnot (bs (qth_program I (current_q (priority_JS_based_execution_aux bs Cs S JS I n))))) (priority_JS_based_execution bs Cs S JS I n'' (qth_program I (current_q (priority_JS_based_execution_aux bs Cs S JS I n))))) 
        \<and> \<not>(\<exists>J \<in> JS n'' (priority_JS_based_execution bs Cs S JS I n''). (qth_program I (current_q (priority_JS_based_execution_aux bs Cs S JS I n)))\<in>J))"
      and "n \<le> n'"
      and JS_nonempty: "\<And>n S.((JS n S) \<noteq> {})"  
  shows "current_q (priority_JS_based_execution_aux bs Cs S JS I n') = current_q (priority_JS_based_execution_aux bs Cs S JS I n) 
        \<and> current_l (priority_JS_based_execution_aux bs Cs S JS I n') = current_l (priority_JS_based_execution_aux bs Cs S JS I n)
        \<and> qth_program I (current_q (priority_JS_based_execution_aux bs Cs S JS I n')) = qth_program I (current_q (priority_JS_based_execution_aux bs Cs S JS I n))"
  using assms
proof (induction n')
  case 0
  then show ?case
    by blast
next
  case (Suc n')
  hence "n= Suc n' \<or> n < Suc n'" by auto
  thus ?case 
  proof
    assume "n= Suc n'"
    thus ?case
      by blast
  next
    assume asm:"n < Suc n'"
    from assms Suc have n'nope:"\<not>(holds_forall (lnot (bs (qth_program I (current_q (priority_JS_based_execution_aux bs Cs S JS I n))))) (priority_JS_based_execution bs Cs S JS I n' (qth_program I (current_q (priority_JS_based_execution_aux bs Cs S JS I n))))) \<and> \<not>(\<exists>J \<in> JS n' (priority_JS_based_execution bs Cs S JS I n'). (qth_program I (current_q (priority_JS_based_execution_aux bs Cs S JS I n)))\<in>J)"
      by (metis asm lessI less_Suc_eq_le)
    obtain Sn l q where
        Haux: "priority_JS_based_execution_aux bs Cs S JS I n' = (Sn,l,q)"
        by (cases "priority_JS_based_execution_aux bs Cs S JS I n'")
    let ?p = "qth_program I q"
    have eq:"q = current_q (priority_JS_based_execution_aux bs Cs S JS I n')"
      by(auto simp add:Haux)
    have eq2:"l = current_l (priority_JS_based_execution_aux bs Cs S JS I n')"
      by(auto simp add:Haux)
    have eq3: "Sn = (priority_JS_based_execution bs Cs S JS I n')"
      by(auto simp add:priority_JS_based_execution_def Haux)

    from asm Suc have H1:"current_q (priority_JS_based_execution_aux bs Cs S JS I n') = current_q (priority_JS_based_execution_aux bs Cs S JS I n)"
           and H2:"current_l (priority_JS_based_execution_aux bs Cs S JS I n') = current_l (priority_JS_based_execution_aux bs Cs S JS I n)"
          and H3:"qth_program I (current_q (priority_JS_based_execution_aux bs Cs S JS I n')) = qth_program I (current_q (priority_JS_based_execution_aux bs Cs S JS I n))"
       apply simp using asm Suc
       apply force
      using asm Suc by force
    from n'nope H3 eq
    have pnope:"\<not>(holds_forall (lnot (bs ?p)) (priority_JS_based_execution bs Cs S JS I n' ?p)) \<and> \<not>(\<exists>J \<in> JS n' (priority_JS_based_execution bs Cs S JS I n'). ?p\<in>J)"
      by presburger


    from pnope priority_picker_inJS[of JS n' "(priority_JS_based_execution bs Cs S JS I n')" ?p ] JS_nonempty[of n' "(priority_JS_based_execution bs Cs S JS I n')"]    
    have pnotin:"?p \<notin> priority_picker JS ?p n' (priority_JS_based_execution bs Cs S JS I n')" 
      by blast
    
      
    have "current_q (priority_JS_based_execution_aux bs Cs S JS I (Suc n')) = current_q (priority_JS_based_execution_aux bs Cs S JS I n)"
      apply(auto simp add:Haux Let_def eq3 pnotin pnope)
      by(auto simp add:eq H1)

    moreover have "current_l (priority_JS_based_execution_aux bs Cs S JS I (Suc n')) = current_l (priority_JS_based_execution_aux bs Cs S JS I n)"
      apply(auto simp add:Haux Let_def eq3 pnotin pnope)
      by(auto simp add:eq2 H2)

    moreover have "qth_program I (current_q (priority_JS_based_execution_aux bs Cs S JS I (Suc n'))) = qth_program I (current_q (priority_JS_based_execution_aux bs Cs S JS I n))"
      apply(auto simp add:Haux Let_def eq3 pnotin pnope)
      by(auto simp add:eq H1)
      
    ultimately show ?case by auto
  qed
qed


lemma qth_exists:
  fixes I :: "nat set"
  assumes "q \<in> valid_qs I"
    and "I \<noteq> {}"
  shows "\<exists>i. i \<in> I \<and> card {j \<in> I. j < i} = q"
  using assms
proof (induction q arbitrary: I)
  case 0

  define i where "i = (LEAST i. i \<in> I)"
  have iI: "i \<in> I"
    unfolding i_def using \<open>I \<noteq> {}\<close>
    using LeastI_ex
    by (metis all_not_in_conv)

  have "{j \<in> I. j < i} = {}"
  proof auto
    fix j
    assume "j \<in> I" and "j < i"
    moreover from \<open>j \<in> I\<close> have "i \<le> j"
      unfolding i_def by (rule Least_le)
    ultimately show False by simp
  qed

  with iI show ?case by auto
next
  case (Suc q)
  have q_valid: "q \<in> valid_qs I"
    using Suc.prems by (auto split: if_splits)

  from Suc.IH[OF q_valid]
  obtain k where kI: "k \<in> I" and k_card: "card {j \<in> I. j < k} = q"
    using Suc.prems(2) by blast

  let ?A = "{i \<in> I. k < i}"

  have fin_k: "finite {j \<in> I. j < k}"
    by (rule finite_subset[OF _ finite_lessThan]) auto

  have A_ne: "?A \<noteq> {}"
  proof
    assume A_empty: "?A = {}"

    have I_eq: "I = insert k {j \<in> I. j < k}"
    proof
      show "I \<subseteq> insert k {j \<in> I. j < k}"
      proof
        fix i assume iI: "i \<in> I"
        show "i \<in> insert k {j \<in> I. j < k}"
        proof (cases "i < k")
          case True
          with iI show ?thesis by auto
        next
          case False
          show ?thesis
          proof (cases "i = k")
            case True
            then show ?thesis by simp
          next
            case False
            from False \<open>\<not> i < k\<close> have "k < i" by auto
            with iI A_empty show ?thesis by auto
          qed
        qed
      qed
    next
      show "insert k {j \<in> I. j < k} \<subseteq> I"
        using kI by auto
    qed

    have finI: "finite I"
      using fin_k I_eq
      using finite.simps by blast

    have "card I = Suc q"
      using I_eq kI k_card fin_k
      by (metis card_insert_disjoint less_not_refl mem_Collect_eq)

    with Suc.prems finI show False
      by simp
  qed

  define i where "i = (LEAST i. i \<in> ?A)"
  have iA: "i \<in> ?A"
    unfolding i_def using A_ne LeastI_ex
    by (metis (mono_tags, lifting) Collect_empty_eq mem_Collect_eq)
  then have iI: "i \<in> I" and ki: "k < i"
    by auto

  have no_between: "j \<in> I \<Longrightarrow> j < i \<Longrightarrow> j \<le> k" for j
  proof -
    assume jI: "j \<in> I" and ji: "j < i"
    show "j \<le> k"
    proof (rule ccontr)
      assume "\<not> j \<le> k"
      then have "k < j" by simp
      with jI have "j \<in> ?A" by simp
      then have "i \<le> j"
        unfolding i_def by (rule Least_le)
      with ji show False by simp
    qed
  qed

  have pred_i: "{j \<in> I. j < i} = insert k {j \<in> I. j < k}"
  proof
    show "{j \<in> I. j < i} \<subseteq> insert k {j \<in> I. j < k}"
    proof
      fix j assume "j \<in> {j \<in> I. j < i}"
      then have jI: "j \<in> I" and ji: "j < i" by auto
      from no_between[OF jI ji] show "j \<in> insert k {j \<in> I. j < k}"
        using jI by force
    qed
  next
    show "insert k {j \<in> I. j < k} \<subseteq> {j \<in> I. j < i}"
      using kI ki by auto
  qed

  have "card {j \<in> I. j < i} = Suc q"
    using pred_i kI k_card fin_k by simp

  with iI show ?case by blast
qed


lemma qth_unique:
  fixes I :: "nat set"
  assumes "i \<in> I" "card {j \<in> I. j < i} = q"
      and "k \<in> I" "card {j \<in> I. j < k} = q"
  shows "i = k"
proof (rule ccontr)
  assume "i \<noteq> k"
  then consider "i < k" | "k < i"
    by linarith
  then show False
  proof cases
    case 1
    let ?A = "{j \<in> I. j < i}"
    let ?B = "{j \<in> I. j < k}"
    have "finite ?B"
      by (rule finite_subset[OF _ finite_lessThan]) auto
    moreover have "?A \<subset> ?B"
      using assms 1 by auto
    ultimately have "card ?A < card ?B"
      by (rule psubset_card_mono)
    with assms show False by simp
  next
    case 2
    let ?A = "{j \<in> I. j < k}"
    let ?B = "{j \<in> I. j < i}"
    have "finite ?B"
      by (rule finite_subset[OF _ finite_lessThan]) auto
    moreover have "?A \<subset> ?B"
      using assms 2 by auto
    ultimately have "card ?A < card ?B"
      by (rule psubset_card_mono)
    with assms show False by simp
  qed
qed


lemma ex1_qth_program:
  fixes I :: "nat set"
  assumes "q \<in> valid_qs I"
    and "I \<noteq> {}"
  shows "\<exists>!i. i \<in> I \<and> card {j \<in> I. j < i} = q"
  using qth_exists[OF assms] qth_unique by blast


lemma qth_program_in:
  assumes "q \<in> valid_qs I"
      and "I \<noteq> {}"
  shows "qth_program I q \<in> I"
proof -
  have "(THE i. i \<in> I \<and> card {j \<in> I. j < i} = q) \<in> I \<and>
        card {j \<in> I. j < (THE i. i \<in> I \<and> card {j \<in> I. j < i} = q)} = q"
    using ex1_qth_program[OF assms]
    by (rule theI')
  then show ?thesis
    unfolding qth_program_def by simp
qed



lemma lm2:
  assumes "(\<forall>i\<in>I. (\<exists>n'\<ge>n. (holds_forall (lnot (bs i)) (priority_JS_based_execution bs Cs S JS I n' i)) \<or> (\<exists>J \<in> JS n' (priority_JS_based_execution bs Cs S JS I n'). i\<in>J)))"
   and JS_nonempty: "\<And>n S.((JS n S) \<noteq> {})"  
   and "I \<noteq> {}"
 shows "\<forall>i\<in>valid_qs I. current_q (priority_JS_based_execution_aux bs Cs S JS I n) = i \<longrightarrow> (Suc i) < current_l (priority_JS_based_execution_aux bs Cs S JS I n) 
  \<longrightarrow> (\<exists>n'>n. current_q (priority_JS_based_execution_aux bs Cs S JS I n') = (Suc i) 
              \<and> current_l (priority_JS_based_execution_aux bs Cs S JS I n') = current_l (priority_JS_based_execution_aux bs Cs S JS I n))"
proof (intro impI ballI)
  fix i
  assume asm1:"i \<in> valid_qs I"
  assume asm2:"(Suc i) < current_l (priority_JS_based_execution_aux bs Cs S JS I n)"
  assume asm3:"current_q (priority_JS_based_execution_aux bs Cs S JS I n) = i"
  show "\<exists>n'>n.
                 current_q (priority_JS_based_execution_aux bs Cs S JS I n') = Suc i \<and>
                 current_l (priority_JS_based_execution_aux bs Cs S JS I n') = current_l (priority_JS_based_execution_aux bs Cs S JS I n)"
  proof -
    obtain Sn l q where
      Haux: "priority_JS_based_execution_aux bs Cs S JS I n = (Sn,l,q)"
      by (cases "priority_JS_based_execution_aux bs Cs S JS I n")
    let ?p = "qth_program I q"
    have eq:"q = current_q (priority_JS_based_execution_aux bs Cs S JS I n)"
      by(auto simp add:Haux)
    have eq2:"l = current_l (priority_JS_based_execution_aux bs Cs S JS I n)"
      by(auto simp add:Haux)
    have "?p \<in> I" using qth_program_in assms(3) q_belonging_lemma
      using eq by blast
    with assms(1) have "\<exists>n'\<ge>n. (holds_forall (lnot (bs ?p)) (priority_JS_based_execution bs Cs S JS I n' ?p)) \<or> (\<exists>J \<in> JS n' (priority_JS_based_execution bs Cs S JS I n'). ?p\<in>J)"
      by blast
    have "\<exists>n'\<ge>n. ((holds_forall (lnot (bs ?p)) (priority_JS_based_execution bs Cs S JS I n' ?p)) \<or> (\<exists>J \<in> JS n' (priority_JS_based_execution bs Cs S JS I n'). ?p\<in>J)) 
          \<and> (\<forall>n''<n'. \<not>( n''\<ge>n \<and> ((holds_forall (lnot (bs ?p)) (priority_JS_based_execution bs Cs S JS I n'' ?p)) \<or> (\<exists>J \<in> JS n'' (priority_JS_based_execution bs Cs S JS I n''). ?p\<in>J))))"
      using least_one_exists[of "(\<lambda>n''. n''\<ge>n \<and> ((holds_forall (lnot (bs ?p)) (priority_JS_based_execution bs Cs S JS I n'' ?p)) \<or> (\<exists>J \<in> JS n'' (priority_JS_based_execution bs Cs S JS I n''). ?p\<in>J)))"]
      using \<open>qth_program I q \<in> I\<close> assms(1) by auto
    from this obtain n' where greater:"n'\<ge>n" and n'prop:"(holds_forall (lnot (bs ?p)) (priority_JS_based_execution bs Cs S JS I n' ?p)) \<or> (\<exists>J \<in> JS n' (priority_JS_based_execution bs Cs S JS I n'). ?p\<in>J)" 
          and noo:"(\<forall>n''<n'. \<not>( n''\<ge>n \<and> ((holds_forall (lnot (bs ?p)) (priority_JS_based_execution bs Cs S JS I n'' ?p)) \<or> (\<exists>J \<in> JS n'' (priority_JS_based_execution bs Cs S JS I n''). ?p\<in>J))))"
      by blast

    have H1:"current_l (priority_JS_based_execution_aux bs Cs S JS I n') = current_l (priority_JS_based_execution_aux bs Cs S JS I n)"
      using l_q_preservation noo greater eq JS_nonempty by (smt (verit, best))
    have H2:"current_q (priority_JS_based_execution_aux bs Cs S JS I n') = current_q (priority_JS_based_execution_aux bs Cs S JS I n)"
      using l_q_preservation noo greater eq JS_nonempty by (smt (verit, best))


    obtain Sn' l' q' where
      Haux': "priority_JS_based_execution_aux bs Cs S JS I n' = (Sn',l',q')"
      by (cases "priority_JS_based_execution_aux bs Cs S JS I n'")

    let ?p' = "qth_program I q'"
    have eq':"q' = current_q (priority_JS_based_execution_aux bs Cs S JS I n')"
      by(auto simp add:Haux')
    have eq2':"l' = current_l (priority_JS_based_execution_aux bs Cs S JS I n')"
      by(auto simp add:Haux')
    have "?p = ?p'" 
      by (simp add: H2 eq eq')

    have "q = q'" 
      by(simp only:eq eq' H2)

    have "l = l'" 
      by(simp only:eq2 eq2' H1)
    from asm2 have "Suc q < l" 
      using Haux asm3 by fastforce
    hence "Suc q' < l'" 
      using \<open>l = l'\<close> \<open>q = q'\<close> by auto

    have qprog:"current_q (priority_JS_based_execution_aux bs Cs S JS I (Suc n')) = (Suc q)"
      apply(auto simp add:Haux' Let_def)
      apply (auto simp add: H2 eq eq')
      apply (metis Haux Haux' n'prop priority_JS_based_execution_def priority_picker_contains_p split_pairs)
      using H1 Haux' asm2 asm3 apply auto[1]
      using H1 Haux' asm2 asm3 apply force
      using H1 Haux' asm2 asm3 by force

    have lstay:"current_l (priority_JS_based_execution_aux bs Cs S JS I (Suc n')) = current_l (priority_JS_based_execution_aux bs Cs S JS I n')"
      apply(auto simp add: Haux' Let_def)
      using H1 H2 Haux' asm2 asm3 apply auto[1]
      using \<open>Suc q' < l'\<close> by auto
      
    have "(Suc n') > n"
      using greater by auto
    have " current_q (priority_JS_based_execution_aux bs Cs S JS I (Suc n')) = Suc q \<and>
       current_l (priority_JS_based_execution_aux bs Cs S JS I (Suc n')) = current_l (priority_JS_based_execution_aux bs Cs S JS I n)"
      using H1 lstay qprog by presburger
    thus ?thesis using \<open>(Suc n') > n\<close>
      using asm3 eq by blast
  qed
qed


lemma all_q_revisited2:
  assumes "(\<forall>n. (\<forall>i\<in>I. (\<exists>n'\<ge>n. (holds_forall (lnot (bs i)) (priority_JS_based_execution bs Cs S JS I n' i)) \<or> (\<exists>J \<in> JS n' (priority_JS_based_execution bs Cs S JS I n'). i\<in>J))))"
   and JS_nonempty: "\<And>n S.((JS n S) \<noteq> {})"
   and "I \<noteq> {}"
  shows "current_q (priority_JS_based_execution_aux bs Cs S JS I n) = q \<and> current_l (priority_JS_based_execution_aux bs Cs S JS I n) = l \<longrightarrow> (\<forall>i\<in>(valid_qs I). i<l \<and> i\<ge>q \<longrightarrow> (\<exists>n'\<ge>n. current_l (priority_JS_based_execution_aux bs Cs S JS I n') = l \<and> current_q (priority_JS_based_execution_aux bs Cs S JS I n') = i))"
proof (intro impI, elim conjE, intro allI ballI impI, elim conjE)
  assume asm1:"current_q (priority_JS_based_execution_aux bs Cs S JS I n) = q"
  assume asm2:"current_l (priority_JS_based_execution_aux bs Cs S JS I n) = l"
  fix i
  assume asm3:"i \<in> valid_qs I"
  assume asm4:"i < l"
  assume asm5:"q \<le> i"
  show "\<exists>n'\<ge>n. current_l (priority_JS_based_execution_aux bs Cs S JS I n') = l \<and> current_q (priority_JS_based_execution_aux bs Cs S JS I n') = i" 
    using asm1 asm2 asm3 asm4 asm5
  proof(induction "i-q" arbitrary:q n)
    case 0
    hence "i = q"
      using asm1 asm5 by auto
    then show ?case using 0 by auto
  next
    case (Suc x)
    from lm2[of I n bs Cs S JS] assms(1) JS_nonempty assms(3) have
      H:"\<forall>i\<in>valid_qs I.
            current_q (priority_JS_based_execution_aux bs Cs S JS I n) = i \<longrightarrow>
            Suc i < current_l (priority_JS_based_execution_aux bs Cs S JS I n) \<longrightarrow> (\<exists>n'>n. current_q (priority_JS_based_execution_aux bs Cs S JS I n') = Suc i
            \<and> current_l (priority_JS_based_execution_aux bs Cs S JS I n') = current_l (priority_JS_based_execution_aux bs Cs S JS I n))"
      by auto
    from Suc have "q = i \<or> q < i" by auto
    then show ?case 
    proof
      assume "q = i"
      then show ?case
        using Suc  by blast
    next
      assume ssm:"q < i"
      with Suc have "Suc q < l"
        using less_trans_Suc by presburger
      from \<open>q < i\<close> \<open>i \<in> valid_qs I\<close>  have "q \<in> valid_qs I"
        by(auto)
      from Suc \<open>Suc q < l\<close> have "(Suc q) < current_l (priority_JS_based_execution_aux bs Cs S JS I n)" by auto
      from H \<open>q \<in> valid_qs I\<close>  \<open>current_q (priority_JS_based_execution_aux bs Cs S JS I n) = q\<close> \<open>(Suc q) < current_l (priority_JS_based_execution_aux bs Cs S JS I n)\<close>  
      obtain n' where "n'>n" and sucq:"current_q (priority_JS_based_execution_aux bs Cs S JS I n') = Suc q"
                and leq:"current_l (priority_JS_based_execution_aux bs Cs S JS I n') = current_l (priority_JS_based_execution_aux bs Cs S JS I n)"
        by auto
      from Suc have "x = i - Suc q" by auto
      with Suc(1)[of "Suc q" n'] sucq leq \<open>i \<in> valid_qs I\<close> \<open>i < l\<close> ssm
      show ?case by (smt (verit, ccfv_threshold) Suc.prems(2) \<open>n < n'\<close> linorder_not_less nless_le not_less_eq order_less_le_trans)
    qed
  qed
qed



lemma lm:
  assumes "(\<forall>n.(\<forall>i\<in>I. (\<exists>n'\<ge>n. (holds_forall (lnot (bs i)) (priority_JS_based_execution bs Cs S JS I n' i)) \<or> (\<exists>J \<in> JS n' (priority_JS_based_execution bs Cs S JS I n'). i\<in>J))))"
   and JS_nonempty: "\<And>n S.((JS n S) \<noteq> {})"
   and "I \<noteq> {}"
  shows "\<forall>i\<in>valid_qs I. current_l (priority_JS_based_execution_aux bs Cs S JS I n) = (Suc i) \<longrightarrow> (Suc i) \<in> (valid_qs I) \<longrightarrow> (\<exists>n'>n. current_l (priority_JS_based_execution_aux bs Cs S JS I n') = (Suc (Suc i))
          \<and> current_q (priority_JS_based_execution_aux bs Cs S JS I n') = 0)"
proof (intro impI ballI)
  fix i
  assume asm1:"i \<in> valid_qs I"
  assume asm2:"Suc i \<in> valid_qs I"
  assume asm3:"current_l (priority_JS_based_execution_aux bs Cs S JS I n) = (Suc i)"

  obtain Sn l q where
    Haux: "priority_JS_based_execution_aux bs Cs S JS I n = (Sn,l,q)"
    by (cases "priority_JS_based_execution_aux bs Cs S JS I n")
  let ?p = "qth_program I q"
  have eq:"q = current_q (priority_JS_based_execution_aux bs Cs S JS I n)"
    by(auto simp add:Haux)
  have eq2:"l = current_l (priority_JS_based_execution_aux bs Cs S JS I n)"
    by(auto simp add:Haux)

  have "l > 0" using l_gr_0 assms(3) eq2
    by metis

  have "(l-1) \<in> valid_qs I" using l_belonging_lemma[of I bs Cs S JS n] assms(3) eq2
    by simp

  have "l-1 < l" using \<open>l > 0\<close> by auto

  have "q \<le> l-1"
    apply(simp only:eq eq2)
    by (metis Suc_pred' \<open>0 < l\<close> eq2 less_Suc_eq_le q_l_inequality_lemma \<open>I \<noteq> {}\<close>)

  from all_q_revisited2[of I bs Cs S JS n q l] assms 
  have "(\<forall>i\<in>valid_qs I.
             i < l \<and> q \<le> i \<longrightarrow>
             (\<exists>n'\<ge>n.
                 current_l (priority_JS_based_execution_aux bs Cs S JS I n') = l \<and>
                 current_q (priority_JS_based_execution_aux bs Cs S JS I n') = i))"
    using eq eq2 by blast
  with \<open>l-1 < l\<close> \<open>q \<le> l-1\<close> \<open>(l-1) \<in> valid_qs I\<close> obtain n' where "n'\<ge>n" and 
                 newl:"current_l (priority_JS_based_execution_aux bs Cs S JS I n') = l" and
                 newq:"current_q (priority_JS_based_execution_aux bs Cs S JS I n') = i"
    using asm3 eq2 by auto

  obtain Sn' l' q' where
    Haux': "priority_JS_based_execution_aux bs Cs S JS I n' = (Sn',l',q')"
    by (cases "priority_JS_based_execution_aux bs Cs S JS I n'")

  let ?p' = "qth_program I q'"
  have eq':"q' = current_q (priority_JS_based_execution_aux bs Cs S JS I n')"
    by(auto simp add:Haux')
  have eq2':"l' = current_l (priority_JS_based_execution_aux bs Cs S JS I n')"
    by(auto simp add:Haux')

  have "?p' \<in> I" using qth_program_in assms(3) q_belonging_lemma
      using eq' by blast


  with assms(1) \<open>?p' \<in> I\<close> have "\<exists>n''\<ge>n'. (holds_forall (lnot (bs ?p')) (priority_JS_based_execution bs Cs S JS I n'' ?p')) \<or> (\<exists>J \<in> JS n'' (priority_JS_based_execution bs Cs S JS I n''). ?p'\<in>J)"
      by blast
  have "\<exists>n''\<ge>n'. ((holds_forall (lnot (bs ?p')) (priority_JS_based_execution bs Cs S JS I n'' ?p')) \<or> (\<exists>J \<in> JS n'' (priority_JS_based_execution bs Cs S JS I n''). ?p'\<in>J)) 
        \<and> (\<forall>n'''<n''. \<not>( n'''\<ge>n' \<and> ((holds_forall (lnot (bs ?p')) (priority_JS_based_execution bs Cs S JS I n''' ?p')) \<or> (\<exists>J \<in> JS n''' (priority_JS_based_execution bs Cs S JS I n'''). ?p'\<in>J))))"
    using least_one_exists[of "(\<lambda>n'''. n'''\<ge>n' \<and> ((holds_forall (lnot (bs ?p')) (priority_JS_based_execution bs Cs S JS I n''' ?p')) \<or> (\<exists>J \<in> JS n''' (priority_JS_based_execution bs Cs S JS I n'''). ?p'\<in>J)))"]
    using \<open>qth_program I q' \<in> I\<close> assms(1) by auto
  from this obtain n'' where greater:"n''\<ge>n'" and n'prop:"(holds_forall (lnot (bs ?p')) (priority_JS_based_execution bs Cs S JS I n'' ?p')) \<or> (\<exists>J \<in> JS n'' (priority_JS_based_execution bs Cs S JS I n''). ?p'\<in>J)" 
        and noo:"(\<forall>n'''<n''. \<not>( n'''\<ge>n' \<and> ((holds_forall (lnot (bs ?p')) (priority_JS_based_execution bs Cs S JS I n''' ?p')) \<or> (\<exists>J \<in> JS n''' (priority_JS_based_execution bs Cs S JS I n'''). ?p'\<in>J))))"
    by blast

  have H1:"current_l (priority_JS_based_execution_aux bs Cs S JS I n'') = current_l (priority_JS_based_execution_aux bs Cs S JS I n')"
      using l_q_preservation noo greater eq' JS_nonempty by (smt (verit, best))
  have H2:"current_q (priority_JS_based_execution_aux bs Cs S JS I n'') = current_q (priority_JS_based_execution_aux bs Cs S JS I n')"
      using l_q_preservation noo greater eq' JS_nonempty by (smt (verit, best))


  obtain Sn'' l'' q'' where
    Haux'': "priority_JS_based_execution_aux bs Cs S JS I n'' = (Sn'',l'',q'')"
    by (cases "priority_JS_based_execution_aux bs Cs S JS I n''")

  let ?p'' = "qth_program I q''"
  have eq'':"q'' = current_q (priority_JS_based_execution_aux bs Cs S JS I n'')"
    by(auto simp add:Haux'')
  have eq2'':"l'' = current_l (priority_JS_based_execution_aux bs Cs S JS I n'')"
    by(auto simp add:Haux'')
  have eq3'':"Sn'' = priority_JS_based_execution bs Cs S JS I n''"
    by(auto simp add:priority_JS_based_execution_def Haux'')

  have "l = (Suc i)" using asm3 eq2 by simp

  have "\<not> Suc q'' < l''" 
    apply(simp add: eq'' H2 eq2'' H1 eq2' newl eq' newq)
    by (simp add: \<open>l = Suc i\<close>)

  have qeq:"q'' = q'"
    by(simp add:eq' eq'' H2)

  have "l'' \<in> (valid_qs I)" 
    apply(simp only:eq2'' H1 newl \<open>l = (Suc i)\<close>)
    by (simp add: asm2)
  hence nextl:"next_len I l'' = Suc l''"
    by(auto simp add:next_len_def)

  have "current_l (priority_JS_based_execution_aux bs Cs S JS I (Suc n'')) 
          = Suc (current_l (priority_JS_based_execution_aux bs Cs S JS I n''))"
    using \<open>\<not> Suc q'' < l''\<close> nextl
    apply(auto simp add:Haux'' Let_def eq3'')
    using n'prop
    apply(simp only:qeq[symmetric])
    by (simp add: priority_picker_contains_p)

  moreover have "current_q (priority_JS_based_execution_aux bs Cs S JS I (Suc n'')) 
          = 0"
    using \<open>\<not> Suc q'' < l''\<close> nextl
    apply(auto simp add:Haux'' Let_def eq3'')
    using n'prop
    apply(simp only:qeq[symmetric])
    by (simp add: priority_picker_contains_p)

  moreover have "(Suc n'')>n" using \<open>n \<le> n'\<close> greater by auto
  ultimately show "\<exists>n'>n. current_l (priority_JS_based_execution_aux bs Cs S JS I n') = Suc (Suc i) \<and>
                 current_q (priority_JS_based_execution_aux bs Cs S JS I n') = 0" using newl H1 \<open>l = (Suc i)\<close>
    by metis
qed



lemma all_q_revisited1:
  assumes "(\<forall>n. (\<forall>i\<in>I. (\<exists>n'\<ge>n. (holds_forall (lnot (bs i)) (priority_JS_based_execution bs Cs S JS I n' i)) \<or> (\<exists>J \<in> JS n' (priority_JS_based_execution bs Cs S JS I n'). i\<in>J))))"
   and JS_nonempty: "\<And>n S.((JS n S) \<noteq> {})"
   and "I\<noteq>{}"
 shows "current_l (priority_JS_based_execution_aux bs Cs S JS I n) = l \<longrightarrow> (\<forall>i\<in>valid_qs I. (Suc i) > l \<longrightarrow>(\<exists>n'\<ge>n. current_l (priority_JS_based_execution_aux bs Cs S JS I n') = (Suc i) \<and> current_q (priority_JS_based_execution_aux bs Cs S JS I n') = 0))"
proof (intro impI allI ballI)
  assume asm1:"current_l (priority_JS_based_execution_aux bs Cs S JS I n) = l"
  fix i
  assume asm2:"i \<in> valid_qs I"
  assume asm3:"l < Suc i"
  from asm1 l_belonging_lemma assms(3) have H:"(l-1)\<in>valid_qs I" by blast 
  show "\<exists>n'\<ge>n. current_l (priority_JS_based_execution_aux bs Cs S JS I n') = (Suc i) \<and> current_q (priority_JS_based_execution_aux bs Cs S JS I n') = 0" 
    using asm3 asm1 asm2 H
  proof (induction "Suc i - l" arbitrary:l n)
    case 0
    then show ?case by auto
  next
    case (Suc x)
    have "l \<in> valid_qs I" using \<open>i \<in> valid_qs I\<close> \<open>l < Suc i\<close>
      by(auto)
    have "l > 0" using l_gr_0 assms(3) asm1
      by (metis Suc.prems(2))
    hence "Suc (l-1) = l" by simp
    from lm[of I bs Cs S JS n] \<open>(l-1)\<in>valid_qs I\<close> assms
    have "current_l (priority_JS_based_execution_aux bs Cs S JS I n) = Suc (l-1) \<longrightarrow>
       Suc (l-1) \<in> valid_qs I \<longrightarrow>
       (\<exists>n'>n. current_l (priority_JS_based_execution_aux bs Cs S JS I n') = Suc (Suc (l-1)) \<and> current_q (priority_JS_based_execution_aux bs Cs S JS I n') = 0)"
      by auto
    from this have "current_l (priority_JS_based_execution_aux bs Cs S JS I n) = l \<longrightarrow>
       l \<in> valid_qs I \<longrightarrow>
       (\<exists>n'>n. current_l (priority_JS_based_execution_aux bs Cs S JS I n') = Suc (l) \<and> current_q (priority_JS_based_execution_aux bs Cs S JS I n') = 0)"
      by(simp only:\<open>Suc (l-1) = l\<close>)
    from this obtain n' where "n'>n" and ott:"current_l (priority_JS_based_execution_aux bs Cs S JS I n') = Suc (l) \<and> current_q (priority_JS_based_execution_aux bs Cs S JS I n') = 0"
      using Suc \<open>l \<in> valid_qs I\<close> by blast
    from Suc have "x = Suc i - Suc l" 
      by (metis Suc.hyps(2) Suc.prems(1) Suc_diff_Suc nat.inject)
    have "(Suc l) = Suc i \<or> Suc l < Suc i"
      using Suc.prems(1) Suc_lessI by blast
    then show ?case
    proof 
      assume "Suc l = Suc i"
      with ott show ?case
        using \<open>n < n'\<close> less_or_eq_imp_le by blast
    next
      assume "Suc l < Suc i"
      from \<open>l \<in> valid_qs I\<close> \<open>(l-1)\<in>valid_qs I\<close> have "Suc l - 1 \<in> valid_qs I" 
        by(auto)
      have "(\<exists>n'>n.
             current_l (priority_JS_based_execution_aux bs Cs S JS I n') = Suc i \<and> current_q (priority_JS_based_execution_aux bs Cs S JS I n') = 0)"
        using Suc(1)[of "(Suc l)" n'] \<open>x = Suc i - Suc l\<close> \<open>Suc l < Suc i\<close> \<open>Suc l - 1 \<in> valid_qs I\<close> ott
        using \<open>n < n'\<close> order.strict_trans2
        using asm2 by blast
      then show ?case  
        using less_or_eq_imp_le by blast
    qed
  qed
qed


lemma lm3:
  assumes "(\<forall>n.(\<forall>i\<in>I. (\<exists>n'\<ge>n. (holds_forall (lnot (bs i)) (priority_JS_based_execution bs Cs S JS I n' i)) \<or> (\<exists>J \<in> JS n' (priority_JS_based_execution bs Cs S JS I n'). i\<in>J))))"
   and JS_nonempty: "\<And>n S.((JS n S) \<noteq> {})"
   and "I \<noteq> {}"
   and "finite I"
 shows "current_l (priority_JS_based_execution_aux bs Cs S JS I n) = card I \<longrightarrow> 
          (\<exists>n'>n. current_l (priority_JS_based_execution_aux bs Cs S JS I n') = card I
                    \<and> current_q (priority_JS_based_execution_aux bs Cs S JS I n') = 0)"
proof (intro impI ballI)
  assume asm:"current_l (priority_JS_based_execution_aux bs Cs S JS I n) = card I"

  obtain Sn l q where
    Haux: "priority_JS_based_execution_aux bs Cs S JS I n = (Sn,l,q)"
    by (cases "priority_JS_based_execution_aux bs Cs S JS I n")
  let ?p = "qth_program I q"
  have eq:"q = current_q (priority_JS_based_execution_aux bs Cs S JS I n)"
    by(auto simp add:Haux)
  have eq2:"l = current_l (priority_JS_based_execution_aux bs Cs S JS I n)"
    by(auto simp add:Haux)

  have "l > 0" using l_gr_0 assms(3) eq2
  by (metis)

  have "(l-1) \<in> valid_qs I" using l_belonging_lemma[of I bs Cs S JS n] assms(3) eq2
    by simp

  have "l-1 < l" using \<open>l > 0\<close> by auto

  have "q \<le> l-1"
    apply(simp only:eq eq2)
    by (metis Suc_pred' \<open>0 < l\<close> eq2 less_Suc_eq_le q_l_inequality_lemma \<open>I \<noteq> {}\<close>)

  from all_q_revisited2[of I bs Cs S JS n q l] assms 
  have "(\<forall>i\<in>valid_qs I.
             i < l \<and> q \<le> i \<longrightarrow>
             (\<exists>n'\<ge>n.
                 current_l (priority_JS_based_execution_aux bs Cs S JS I n') = l \<and>
                 current_q (priority_JS_based_execution_aux bs Cs S JS I n') = i))"
    using eq eq2 by blast
  with \<open>l-1 < l\<close> \<open>q \<le> l-1\<close> \<open>(l-1) \<in> valid_qs I\<close> obtain n' where "n'\<ge>n" and 
                 newl:"current_l (priority_JS_based_execution_aux bs Cs S JS I n') = l" and
                 newq:"current_q (priority_JS_based_execution_aux bs Cs S JS I n') = (l-1)"
    using asm eq2 by auto

  obtain Sn' l' q' where
    Haux': "priority_JS_based_execution_aux bs Cs S JS I n' = (Sn',l',q')"
    by (cases "priority_JS_based_execution_aux bs Cs S JS I n'")

  let ?p' = "qth_program I q'"
  have eq':"q' = current_q (priority_JS_based_execution_aux bs Cs S JS I n')"
    by(auto simp add:Haux')
  have eq2':"l' = current_l (priority_JS_based_execution_aux bs Cs S JS I n')"
    by(auto simp add:Haux')

  have "?p' \<in> I" using qth_program_in assms(3) q_belonging_lemma
      using eq' by blast


  with assms(1) \<open>?p' \<in> I\<close> have "\<exists>n''\<ge>n'. (holds_forall (lnot (bs ?p')) (priority_JS_based_execution bs Cs S JS I n'' ?p')) \<or> (\<exists>J \<in> JS n'' (priority_JS_based_execution bs Cs S JS I n''). ?p'\<in>J)"
      by blast
  have "\<exists>n''\<ge>n'. ((holds_forall (lnot (bs ?p')) (priority_JS_based_execution bs Cs S JS I n'' ?p')) \<or> (\<exists>J \<in> JS n'' (priority_JS_based_execution bs Cs S JS I n''). ?p'\<in>J)) 
        \<and> (\<forall>n'''<n''. \<not>( n'''\<ge>n' \<and> ((holds_forall (lnot (bs ?p')) (priority_JS_based_execution bs Cs S JS I n''' ?p')) \<or> (\<exists>J \<in> JS n''' (priority_JS_based_execution bs Cs S JS I n'''). ?p'\<in>J))))"
    using least_one_exists[of "(\<lambda>n'''. n'''\<ge>n' \<and> ((holds_forall (lnot (bs ?p')) (priority_JS_based_execution bs Cs S JS I n''' ?p')) \<or> (\<exists>J \<in> JS n''' (priority_JS_based_execution bs Cs S JS I n'''). ?p'\<in>J)))"]
    using \<open>qth_program I q' \<in> I\<close> assms(1) by auto
  from this obtain n'' where greater:"n''\<ge>n'" and n'prop:"(holds_forall (lnot (bs ?p')) (priority_JS_based_execution bs Cs S JS I n'' ?p')) \<or> (\<exists>J \<in> JS n'' (priority_JS_based_execution bs Cs S JS I n''). ?p'\<in>J)" 
        and noo:"(\<forall>n'''<n''. \<not>( n'''\<ge>n' \<and> ((holds_forall (lnot (bs ?p')) (priority_JS_based_execution bs Cs S JS I n''' ?p')) \<or> (\<exists>J \<in> JS n''' (priority_JS_based_execution bs Cs S JS I n'''). ?p'\<in>J))))"
    by blast

  have H1:"current_l (priority_JS_based_execution_aux bs Cs S JS I n'') = current_l (priority_JS_based_execution_aux bs Cs S JS I n')"
      using l_q_preservation noo greater eq' JS_nonempty by (smt (verit, best))
  have H2:"current_q (priority_JS_based_execution_aux bs Cs S JS I n'') = current_q (priority_JS_based_execution_aux bs Cs S JS I n')"
      using l_q_preservation noo greater eq' JS_nonempty by (smt (verit, best))


  obtain Sn'' l'' q'' where
    Haux'': "priority_JS_based_execution_aux bs Cs S JS I n'' = (Sn'',l'',q'')"
    by (cases "priority_JS_based_execution_aux bs Cs S JS I n''")

  let ?p'' = "qth_program I q''"
  have eq'':"q'' = current_q (priority_JS_based_execution_aux bs Cs S JS I n'')"
    by(auto simp add:Haux'')
  have eq2'':"l'' = current_l (priority_JS_based_execution_aux bs Cs S JS I n'')"
    by(auto simp add:Haux'')
  have eq3'':"Sn'' = priority_JS_based_execution bs Cs S JS I n''"
    by(auto simp add:priority_JS_based_execution_def Haux'')

  have "l = card I" using asm eq2 by simp

  have "\<not> Suc q'' < l''" 
    by(simp add: eq'' H2 eq2'' H1 eq2' newl eq' newq)

  have qeq:"q'' = q'"
    by(simp add:eq' eq'' H2)


  hence nextl:"next_len I l'' = l''"
    using assms(4)
    by(auto simp add:next_len_def \<open>l = card I\<close> eq2'' H1 eq2' newl)

  have "current_l (priority_JS_based_execution_aux bs Cs S JS I (Suc n'')) 
          = (current_l (priority_JS_based_execution_aux bs Cs S JS I n''))"
    using \<open>\<not> Suc q'' < l''\<close> nextl
    by(auto simp add:Haux'' Let_def eq3'')

  moreover have "current_q (priority_JS_based_execution_aux bs Cs S JS I (Suc n''))  = 0"
    using \<open>\<not> Suc q'' < l''\<close> nextl
    apply(auto simp add:Haux'' Let_def eq3'')
    using n'prop
    apply(simp only:qeq[symmetric])
    by (simp add: priority_picker_contains_p)

  moreover have "(Suc n'')>n" using \<open>n \<le> n'\<close> greater by auto
  ultimately show "\<exists>n'>n. current_l (priority_JS_based_execution_aux bs Cs S JS I n') = card I \<and>
                 current_q (priority_JS_based_execution_aux bs Cs S JS I n') = 0" using newl H1 \<open>l = card I\<close>
    by metis
qed


lemma all_q_revisited:
  assumes "(\<forall>n. (\<forall>i\<in>I. (\<exists>n'\<ge>n. (holds_forall (lnot (bs i)) (priority_JS_based_execution bs Cs S JS I n' i)) \<or> (\<exists>J \<in> JS n' (priority_JS_based_execution bs Cs S JS I n'). i\<in>J))))"
   and JS_nonempty: "\<And>n S.((JS n S) \<noteq> {})"
   and "I \<noteq> {}"
 shows "\<forall>i \<in> I. \<forall>n. holds_forall_hyper I (lnot_hyper bs) (priority_JS_based_execution bs Cs S JS I n) \<or>  (\<exists>n'\<ge>n. (qth_program I (current_q (priority_JS_based_execution_aux bs Cs S JS I n'))) = i)"
proof -
  have "\<forall>i\<in>valid_qs I. \<forall>n. holds_forall_hyper I (lnot_hyper bs) (priority_JS_based_execution bs Cs S JS I n) \<or> (\<exists>n'\<ge>n. current_q (priority_JS_based_execution_aux bs Cs S JS I n') = i)"
  proof (intro allI ballI)
    fix i n
    assume asm:"i\<in> (if finite I then {0..<card I} else UNIV)"
    from assms have "holds_forall_hyper I (lnot_hyper bs) (priority_JS_based_execution bs Cs S JS I n) \<or>  
  (\<forall>i\<in>I. (\<exists>n'\<ge>n. (holds_forall (lnot (bs i)) (priority_JS_based_execution bs Cs S JS I n' i)) \<or> (\<exists>J \<in> JS n' (priority_JS_based_execution bs Cs S JS I n'). i\<in>J)))" by auto
    thus "holds_forall_hyper I (lnot_hyper bs) (priority_JS_based_execution bs Cs S JS I n) \<or> (\<exists>n'\<ge>n. current_q (priority_JS_based_execution_aux bs Cs S JS I n') = i)"
    proof
      assume "holds_forall_hyper I (lnot_hyper bs) (priority_JS_based_execution bs Cs S JS I n)"
      thus ?thesis by auto
    next 
      assume asm2:"(\<forall>i\<in>I. (\<exists>n'\<ge>n. (holds_forall (lnot (bs i)) (priority_JS_based_execution bs Cs S JS I n' i)) \<or> (\<exists>J \<in> JS n' (priority_JS_based_execution bs Cs S JS I n'). i\<in>J)))"
      show ?thesis
      proof (rule disjI2)
        obtain Sn l q where
          Haux: "priority_JS_based_execution_aux bs Cs S JS I n = (Sn,l,q)"
          by (cases "priority_JS_based_execution_aux bs Cs S JS I n")
        have eq:"q = current_q (priority_JS_based_execution_aux bs Cs S JS I n)"
          by(auto simp add:Haux)
        have eq2:"l = current_l (priority_JS_based_execution_aux bs Cs S JS I n)"
          by(auto simp add:Haux)
        have maxgeq:"(max l (Suc i)) \<ge> l" 
          by auto
        from l_belonging_lemma[of I bs Cs S JS n] assms(3) eq2 asm
        have fincard:"finite I \<longrightarrow> (max l (Suc i)) \<le> card I"
          by(auto)
        have "(\<not> finite I \<or> (finite I \<and> ((max l (Suc i)) < card I) \<or> (Suc i) > l)) \<or> finite I \<and> l = card I" using fincard by auto
        thus "\<exists>n'\<ge>n. current_q (priority_JS_based_execution_aux bs Cs S JS I n') = i"
        proof
          assume asmf:"\<not> finite I \<or> (finite I \<and> ((max l (Suc i)) < card I) \<or> (Suc i) > l)"
          have "Suc (max l (Suc i)) > l" by auto
          have "(max l (Suc i)) \<in> valid_qs I \<or> (max l (Suc i)) > l" using asmf by(auto)
          thus "\<exists>n'\<ge>n. current_q (priority_JS_based_execution_aux bs Cs S JS I n') = i"
          proof
            assume valm:"max l (Suc i) \<in> valid_qs I"
            from valm all_q_revisited1[of I bs Cs S JS n l]  eq2  l_belonging_lemma[of I bs Cs S JS n] assms(3) asm2 JS_nonempty \<open>I \<noteq> {}\<close> \<open>Suc (max l (Suc i)) > l\<close> asm assms(1)
            have "(\<exists>n'\<ge>n. current_l (priority_JS_based_execution_aux bs Cs S JS I n') = Suc (max l (Suc i)) \<and> current_q (priority_JS_based_execution_aux bs Cs S JS I n') = 0)"
              by (metis)
            from this obtain n' where "n'\<ge> n" and "current_l (priority_JS_based_execution_aux bs Cs S JS I n') = Suc (max l (Suc i)) \<and> current_q (priority_JS_based_execution_aux bs Cs S JS I n') = 0"
                      by blast
            with assms(1) all_q_revisited2[of I bs Cs S JS n' 0 "Suc (max l (Suc i))"] JS_nonempty assms(1)
            have "(\<forall>i'\<in>(valid_qs I). i'<Suc (max l (Suc i)) \<and> i'\<ge>0 \<longrightarrow> (\<exists>n''\<ge>n'. current_l (priority_JS_based_execution_aux bs Cs S JS I n'') = Suc (max l (Suc i)) \<and> current_q (priority_JS_based_execution_aux bs Cs S JS I n'') = i'))"
              using assms(3) by blast
            from this \<open>i\<in>(valid_qs I)\<close> obtain n'' where "n''\<ge>n'" and "(current_q (priority_JS_based_execution_aux bs Cs S JS I n'') = i)"
              by fastforce
            thus "\<exists>n'\<ge>n. current_q (priority_JS_based_execution_aux bs Cs S JS I n') = i" using \<open>n''\<ge>n'\<close> \<open>n'\<ge>n\<close>
              using le_trans by blast
          next
            assume "(max l (Suc i)) > l"
            from all_q_revisited1[of I bs Cs S JS n l]  eq2  l_belonging_lemma[of I bs Cs S JS n] assms(3) asm2 JS_nonempty \<open>I \<noteq> {}\<close> \<open>(max l (Suc i)) > l\<close> asm assms(1)
            have "(\<exists>n'\<ge>n. current_l (priority_JS_based_execution_aux bs Cs S JS I n') = (max l (Suc i)) \<and> current_q (priority_JS_based_execution_aux bs Cs S JS I n') = 0)"
              by simp
            from this obtain n' where "n'\<ge> n" and "current_l (priority_JS_based_execution_aux bs Cs S JS I n') =  (max l (Suc i)) \<and> current_q (priority_JS_based_execution_aux bs Cs S JS I n') = 0"
                      by blast
            with assms(1) all_q_revisited2[of I bs Cs S JS n' 0 " (max l (Suc i))"] JS_nonempty assms(1)
            have "(\<forall>i'\<in>(valid_qs I). i'< (max l (Suc i)) \<and> i'\<ge>0 \<longrightarrow> (\<exists>n''\<ge>n'. current_l (priority_JS_based_execution_aux bs Cs S JS I n'') =  (max l (Suc i)) \<and> current_q (priority_JS_based_execution_aux bs Cs S JS I n'') = i'))"
              using assms(3) by blast
            from this \<open>i\<in>(valid_qs I)\<close> obtain n'' where "n''\<ge>n'" and "(current_q (priority_JS_based_execution_aux bs Cs S JS I n'') = i)"
              by fastforce
            thus "\<exists>n'\<ge>n. current_q (priority_JS_based_execution_aux bs Cs S JS I n') = i" using \<open>n''\<ge>n'\<close> \<open>n'\<ge>n\<close>
              using le_trans by blast
          qed
        next
          assume asm:"finite I \<and> l = card I"
          with lm3[of I bs Cs S JS n] eq2
          have "(\<exists>n'>n. current_l (priority_JS_based_execution_aux bs Cs S JS I n') = card I \<and> current_q (priority_JS_based_execution_aux bs Cs S JS I n') = 0)"
            using JS_nonempty assms(1,3) by blast
          from this obtain n' where "n'> n" and "current_l (priority_JS_based_execution_aux bs Cs S JS I n') =  card I \<and> current_q (priority_JS_based_execution_aux bs Cs S JS I n') = 0"
                      by blast
          with assms(1) all_q_revisited2[of I bs Cs S JS n' 0 "card I"] JS_nonempty assms(1)
          have "(\<forall>i'\<in>(valid_qs I). i'< card I \<and> i'\<ge>0 \<longrightarrow> (\<exists>n''\<ge>n'. current_l (priority_JS_based_execution_aux bs Cs S JS I n'') =  card I \<and> current_q (priority_JS_based_execution_aux bs Cs S JS I n'') = i'))"
            using assms(3) by blast
          from this \<open>i\<in>(valid_qs I)\<close> asm obtain n'' where "n''\<ge>n'" and "(current_q (priority_JS_based_execution_aux bs Cs S JS I n'') = i)"
            by fastforce
          thus "\<exists>n'\<ge>n. current_q (priority_JS_based_execution_aux bs Cs S JS I n') = i"
            by (metis \<open>n < n'\<close> dual_order.trans order_less_imp_le)
        qed
      qed
    qed
  qed
  with qs_to_progs show ?thesis by blast
qed

lemma all_programs_reexecuted_or_dead:
  assumes "(\<forall>n. (\<forall>i\<in>I. (\<exists>n'\<ge>n. (holds_forall (lnot (bs i)) (priority_JS_based_execution bs Cs S JS I n' i)) \<or> (\<exists>J \<in> JS n' (priority_JS_based_execution bs Cs S JS I n'). i\<in>J))))"
    and "\<forall>i \<in> I. \<forall>n. holds_forall_hyper I (lnot_hyper bs) (priority_JS_based_execution bs Cs S JS I n) \<or> (\<exists>n'\<ge>n. (qth_program I (current_q (priority_JS_based_execution_aux bs Cs S JS I n'))) = i)"
    and JS_nonempty: "\<And>n S.((JS n S) \<noteq> {})"
  shows "\<forall>i\<in>I. \<forall>n. \<not>(holds_forall (lnot (bs i)) (priority_JS_based_execution bs Cs S JS I n i)) \<longrightarrow> 
      (\<exists>n'\<ge>n. (\<exists>J \<in> JS n' (priority_JS_based_execution bs Cs S JS I n'). i \<in> J \<and>
        priority_JS_based_execution bs Cs S JS I (Suc n') = sem_rel [i \<mapsto> if_then_else_skip (bs i) (Cs i) | i \<in> J] (priority_JS_based_execution bs Cs S JS I n')))"
proof (intro allI ballI impI)
  fix i n
  assume asm1:"i\<in>I"
  assume asm2:"\<not> holds_forall (lnot (bs i)) (priority_JS_based_execution bs Cs S JS I n i)"
  hence H:"\<not>holds_forall_hyper I (lnot_hyper bs) (priority_JS_based_execution bs Cs S JS I n)"
    using asm1
    by(auto simp add:holds_forall_def lnot_def holds_forall_hyper_def lnot_hyper_def)
  from asm1 H assms(2) obtain n' where "(n'\<ge>n)" and  n'prop:"((qth_program I (current_q (priority_JS_based_execution_aux bs Cs S JS I n'))) = i)"
    by auto
  have "(\<exists>n''\<ge>n. n'' < n' \<and> (\<exists>J \<in> JS n'' (priority_JS_based_execution bs Cs S JS I n''). i \<in> J \<and>
        priority_JS_based_execution bs Cs S JS I (Suc n'') = sem_rel [i \<mapsto> if_then_else_skip (bs i) (Cs i) | i \<in> J] (priority_JS_based_execution bs Cs S JS I n'')))
        \<or> \<not>(\<exists>n''\<ge>n. n'' < n' \<and> (\<exists>J \<in> JS n'' (priority_JS_based_execution bs Cs S JS I n''). i \<in> J \<and>
        priority_JS_based_execution bs Cs S JS I (Suc n'') = sem_rel [i \<mapsto> if_then_else_skip (bs i) (Cs i) | i \<in> J] (priority_JS_based_execution bs Cs S JS I n'')))"
    by auto
  thus "(\<exists>n'\<ge>n. (\<exists>J \<in> JS n' (priority_JS_based_execution bs Cs S JS I n'). i \<in> J \<and>
        priority_JS_based_execution bs Cs S JS I (Suc n') = sem_rel [i \<mapsto> if_then_else_skip (bs i) (Cs i) | i \<in> J] (priority_JS_based_execution bs Cs S JS I n')))"
  proof
    assume "(\<exists>n''\<ge>n. n'' < n' \<and> (\<exists>J \<in> JS n'' (priority_JS_based_execution bs Cs S JS I n''). i \<in> J \<and>
        priority_JS_based_execution bs Cs S JS I (Suc n'') = sem_rel [i \<mapsto> if_then_else_skip (bs i) (Cs i) | i \<in> J] (priority_JS_based_execution bs Cs S JS I n'')))"
    thus ?thesis by auto
  next
    assume asm:"\<not>(\<exists>n''\<ge>n. n'' < n' \<and> (\<exists>J \<in> JS n'' (priority_JS_based_execution bs Cs S JS I n''). i \<in> J \<and>
        priority_JS_based_execution bs Cs S JS I (Suc n'') = sem_rel [i \<mapsto> if_then_else_skip (bs i) (Cs i) | i \<in> J] (priority_JS_based_execution bs Cs S JS I n'')))"
    from \<open>n'\<ge>n\<close> asm state_preservation[of n n' JS bs Cs S I i] JS_nonempty have "(priority_JS_based_execution bs Cs S JS I n') i = (priority_JS_based_execution bs Cs S JS I n) i"
      by blast
    with asm2 have H2:"\<not> holds_forall (lnot (bs i)) (priority_JS_based_execution bs Cs S JS I n' i)" by auto
    hence H:"\<not>holds_forall_hyper I (lnot_hyper bs) (priority_JS_based_execution bs Cs S JS I n')"
      using asm1
      by(auto simp add:holds_forall_def lnot_def holds_forall_hyper_def lnot_hyper_def)
    with assms(1) asm1 obtain n'' where "(n''\<ge>n')" and n''prop:"(holds_forall (lnot (bs i)) (priority_JS_based_execution bs Cs S JS I n'' i)) \<or> (\<exists>J \<in> JS n'' (priority_JS_based_execution bs Cs S JS I n''). i\<in>J)"
      by blast
    have "(\<exists>n'''\<ge>n'. n''' < n'' \<and> (\<exists>J \<in> JS n''' (priority_JS_based_execution bs Cs S JS I n'''). i \<in> J \<and>
      priority_JS_based_execution bs Cs S JS I (Suc n''') = sem_rel [i \<mapsto> if_then_else_skip (bs i) (Cs i) | i \<in> J] (priority_JS_based_execution bs Cs S JS I n''')))
      \<or> \<not>(\<exists>n'''\<ge>n'. n''' < n'' \<and> (\<exists>J \<in> JS n''' (priority_JS_based_execution bs Cs S JS I n'''). i \<in> J \<and>
      priority_JS_based_execution bs Cs S JS I (Suc n''') = sem_rel [i \<mapsto> if_then_else_skip (bs i) (Cs i) | i \<in> J] (priority_JS_based_execution bs Cs S JS I n''')))"
    by auto
    thus ?thesis 
    proof
      assume "(\<exists>n'''\<ge>n'. n''' < n'' \<and> (\<exists>J \<in> JS n''' (priority_JS_based_execution bs Cs S JS I n'''). i \<in> J \<and>
      priority_JS_based_execution bs Cs S JS I (Suc n''') = sem_rel [i \<mapsto> if_then_else_skip (bs i) (Cs i) | i \<in> J] (priority_JS_based_execution bs Cs S JS I n''')))"
      thus ?thesis using \<open>n \<le> n'\<close>
        by (meson dual_order.trans)
    next
      assume asm:"\<not>(\<exists>n'''\<ge>n'. n''' < n'' \<and> (\<exists>J \<in> JS n''' (priority_JS_based_execution bs Cs S JS I n'''). i \<in> J \<and>
      priority_JS_based_execution bs Cs S JS I (Suc n''') = sem_rel [i \<mapsto> if_then_else_skip (bs i) (Cs i) | i \<in> J] (priority_JS_based_execution bs Cs S JS I n''')))"
      from \<open>n''\<ge>n'\<close>  asm state_preservation[of n' n'' JS bs Cs S I i] JS_nonempty have spres:"\<forall>n. n'\<le>n \<and> n \<le> n'' \<longrightarrow> (priority_JS_based_execution bs Cs S JS I n) i = (priority_JS_based_execution bs Cs S JS I n') i"
        by blast
      with \<open>n' \<le> n''\<close> have "(priority_JS_based_execution bs Cs S JS I n'') i = (priority_JS_based_execution bs Cs S JS I n') i"
        by blast
      with H2 have H4:"\<not> holds_forall (lnot (bs i)) (priority_JS_based_execution bs Cs S JS I n'' i)" by auto
      with n''prop have H3:"(\<exists>J\<in>JS n'' (priority_JS_based_execution bs Cs S JS I n''). i \<in> J)" by auto
      from priority_JS_based_execution_step_strong JS_nonempty obtain J'' where eq:"priority_JS_based_execution bs Cs S JS I (Suc n'') = sem_rel [i \<mapsto> if_then_else_skip (bs i) (Cs i) | i \<in> J''] (priority_JS_based_execution bs Cs S JS I n'')"
                                                                     and jinJS:"J'' \<in> JS n''(priority_JS_based_execution bs Cs S JS I n'')" 
                                                                     and priorJS:"qth_program I (current_q (priority_JS_based_execution_aux bs Cs S JS I n'')) \<in> J''
                                                                          \<or> (\<forall>J'' \<in> JS n''(priority_JS_based_execution bs Cs S JS I n''). qth_program I (current_q (priority_JS_based_execution_aux bs Cs S JS I n'')) \<notin>J'')"
        by blast
      
      from \<open>n' \<le> n''\<close>  asm spres H4 have "qth_program I (current_q (priority_JS_based_execution_aux bs Cs S JS I n'')) = i" 
      proof(induction n'')
        case 0
        hence "n' = 0" by auto
        with n'prop show ?case by auto
      next
        case (Suc n'')
        from Suc have "n' = Suc n'' \<or> n' < Suc n''"
          by linarith
        then show ?case 
        proof
          assume "n' = Suc n''"
          with n'prop show ?case by auto
        next
          assume "n' < Suc n''"
          hence "n' \<le> n''" by auto 
          with Suc have nseq:"priority_JS_based_execution bs Cs S JS I n'' i = priority_JS_based_execution bs Cs S JS I (Suc n'') i"
            by (metis le_refl lessI nless_le)
          from Suc have "\<forall>n. n' \<le> n \<and> n \<le> n'' \<longrightarrow> priority_JS_based_execution bs Cs S JS I n i = priority_JS_based_execution bs Cs S JS I n' i"
            by (meson le_imp_less_Suc nless_le)
          moreover from Suc have "\<not> (\<exists>n'''\<ge>n'. n''' < n'' \<and>(\<exists>J\<in>JS n''' (priority_JS_based_execution bs Cs S JS I n'''). i \<in> J \<and>priority_JS_based_execution bs Cs S JS I (Suc n''') = sem_rel (map_comprehension (\<lambda>i. if_then_else_skip (bs i) (Cs i)) (\<lambda>i. i \<in> J)) (priority_JS_based_execution bs Cs S JS I n''')))" 
            using less_SucI by presburger
          moreover from nseq Suc have "\<not> holds_forall (lnot (bs i)) (priority_JS_based_execution bs Cs S JS I n'' i)"
            by presburger
          ultimately have H:"qth_program I (current_q (priority_JS_based_execution_aux bs Cs S JS I n'')) = i" 
            using \<open>n' \<le> n''\<close>
            using Suc.IH by blast
          thus ?case
          proof -
            obtain Sn l q where
              Haux: "priority_JS_based_execution_aux bs Cs S JS I n'' = (Sn,l,q)"
              by (cases "priority_JS_based_execution_aux bs Cs S JS I n''")
            let ?p = "qth_program I q"
            let ?J = "priority_picker JS ?p n'' Sn"
            have eq:"q = current_q (priority_JS_based_execution_aux bs Cs S JS I n'')"
              by(auto simp add:Haux)
            have eq2:"Sn = priority_JS_based_execution bs Cs S JS I n''" unfolding priority_JS_based_execution_def
              by(auto simp add:Haux)
            have eq3: "?p = i"
              by(simp only:eq H)
            have jin:"?J \<in> JS n'' (priority_JS_based_execution bs Cs S JS I n'')" 
              apply(simp only:eq2) 
              using JS_nonempty priority_picker_inJS by metis
            have step:"(priority_JS_based_execution bs Cs S JS I (Suc n'')) = sem_rel [i \<mapsto> if_then_else_skip (bs i) (Cs i) | i \<in> ?J] (priority_JS_based_execution bs Cs S JS I n'')"
              apply(simp only: eq2[symmetric]) unfolding priority_JS_based_execution_def
              using Haux
              by(auto simp add:Let_def)
            have "\<not>?p \<in> ?J" 
              apply(simp only:eq3) using Suc.prems(2) jin step
              using \<open>n' \<le> n''\<close> eq3 by blast
            moreover have "\<not>holds_forall (lnot (bs ?p)) (Sn ?p)" 
              apply(simp only:eq H eq2 nseq)
              by (simp add: Suc.prems(4))
            ultimately show ?thesis using H Haux
              by(auto simp add:Let_def)
          qed
        qed
      qed
      with H3 priorJS have "i \<in> J''" by auto
      with jinJS eq \<open>n''\<ge>n'\<close> \<open>n'\<ge>n\<close> show ?thesis
        by (meson le_trans)
    qed
  qed
qed



text\<open>WhileNonfixedLck\<close>
theorem while_nonfixed_lck:
  assumes   "\<forall>n. \<forall>J\<in>(Pow I - {{}}). \<Turnstile> { conj (Iv n) (V J)} [[i \<mapsto> if_then_else_skip (bs i) (Cs i) | i \<in> J]] { Iv (Suc n) }"
      and   "progress_side_condition1 Iv I bs V"
      and   "progress_side_condition2 Iv I bs V"
      and   "\<forall>n. \<Turnstile> { (Iv n) } [[i \<mapsto> Assume (lnot (bs i)) | i \<in> I]] { Q }"
      and   "relational_upwards_closed I (\<lambda>n. Q) Q_inf"
      and   "I \<noteq> {}"
    shows   "\<Turnstile> { (Iv 0) } [[ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ]] { conj Q_inf (holds_forall_hyper I (lnot_hyper bs))}"
proof(intro relational_hyper_hoare_tripleI)
  fix S
  assume "Iv 0 S"

  from assms(2) assms(6) progress_side_condition1_exists_out 
  have H:"\<forall>n. \<forall>S. \<exists>J\<in>(Pow I - {{}}). (Iv n) S \<longrightarrow> ((disj (V J) (holds_forall_hyper I (lnot_hyper bs))) S)" by metis
  have "\<forall>n. \<forall>S. \<exists>J_set\<subseteq>(Pow I - {{}}). J_set \<noteq>{} \<and> (\<forall>J\<in>J_set. (Iv n) S \<longrightarrow> ((disj (V J) (holds_forall_hyper I (lnot_hyper bs))) S))
        \<and> (\<forall>J\<in>(Pow I - {{}}). (V J) S \<longrightarrow> J \<in> J_set)" 
  proof (intro allI)
    fix n S
    from H obtain J where
      Jmem: "J \<in> Pow I - {{}}"
      and Jprop: "(Iv n) S \<longrightarrow> ((disj (V J) (holds_forall_hyper I (lnot_hyper bs))) S)"
      by blast
    let ?J_set = "{J} \<union> {J'\<in>(Pow I - {{}}). (V J') S}"
    have "?J_set \<subseteq> (Pow I - {{}})"
      using Jmem by auto
    moreover have "?J_set \<noteq> {}"
      by auto
    moreover have "\<forall>K\<in>?J_set. (Iv n) S \<longrightarrow> ((disj (V K) (holds_forall_hyper I (lnot_hyper bs))) S)"
      using Jprop
      by (simp add: disj_def)
    ultimately show "\<exists>J_set\<subseteq>(Pow I - {{}}).
        J_set \<noteq> {} \<and>
        (\<forall>J\<in>J_set. (Iv n) S \<longrightarrow> ((disj (V J) (holds_forall_hyper I (lnot_hyper bs))) S)) \<and> (\<forall>J\<in>(Pow I - {{}}). (V J) S \<longrightarrow> J \<in> J_set)"
      by blast
  qed 
  from this obtain JS where JS_subset:"\<And>n S. ((JS n S) \<subseteq> (Pow I - {{}}))" 
                        and JS_nonempty:"\<And>n S.((JS n S) \<noteq> {})" 
                        and JS_prop:"\<And>n S. (\<forall>J\<in>(JS n S). (Iv n) S \<longrightarrow> ((disj (V J) (holds_forall_hyper I (lnot_hyper bs))) S))"
                        and JS_prop2:"\<And>n S. (\<forall>J\<in>(Pow I - {{}}). (V J) S \<longrightarrow> J \<in> (JS n S))"
    by metis

  let ?Ss = "priority_JS_based_execution bs Cs S JS I"
  let ?Ss' = "\<lambda>n. sem_rel [i \<mapsto> Assume (lnot (bs i)) | i \<in> I] (?Ss n)"
  let ?after_n = "sem_lifted_after_n_steps bs Cs S I"
  let ?after_n_finished = "\<lambda>n. sem_rel [i \<mapsto> Assume (lnot (bs i)) | i \<in> I] (?after_n n)"

  have jsexec_ivq:"(\<forall>n::nat. ((Iv n) (?Ss n) \<or> holds_forall_hyper I (lnot_hyper bs) (?Ss n)) \<and> (Q (?Ss' n)))" 
  proof 
    fix n
    show "((Iv n) (?Ss n) \<or> holds_forall_hyper I (lnot_hyper bs) (?Ss n)) \<and> (Q (?Ss' n))"
    proof (induction n)
      case 0
      then show "((Iv 0) (?Ss 0) \<or> holds_forall_hyper I (lnot_hyper bs) (?Ss 0)) \<and> (Q (?Ss' 0))" using \<open>Iv 0 S\<close> priority_JS_based_execution_base
        by (metis assms(4) relational_hyper_hoare_tripleE)
    next
      case (Suc n)
      from priority_JS_based_execution_step_strong JS_nonempty obtain J' where eq:"?Ss (Suc n) = sem_rel [i \<mapsto> if_then_else_skip (bs i) (Cs i) | i \<in> J'] (?Ss n)"
                                                                           and jinJS:"J' \<in> JS n (?Ss n)" by blast
      have jin:"J' \<in> Pow I - {{}}" using jinJS JS_subset[of "n" "?Ss n"]
        by blast
      from Suc have "(((Iv n) (?Ss n) \<and> \<not>holds_forall_hyper I (lnot_hyper bs) (?Ss n)) \<or> holds_forall_hyper I (lnot_hyper bs) (?Ss n))" by auto
      from this show ?case
      proof
        assume asm1: "((Iv n) (?Ss n) \<and> \<not>holds_forall_hyper I (lnot_hyper bs) (?Ss n))"
        with JS_prop jinJS have vj:"(V J') (?Ss n)"
          by (metis disj_def)
        have "\<Turnstile> {conj (Iv n) (V J')} [[i \<mapsto> if_then_else_skip (bs i) (Cs i) | i \<in> J']] {Iv (Suc n)}"
          using assms(1) jin by auto
        with asm1 vj have H:"Iv (Suc n) (?Ss (Suc n))" unfolding relational_hyper_hoare_triple_def conj_def 
          by (simp add: eq)
        with assms(4) have "Q (?Ss' (Suc n))" 
          using relational_hyper_hoare_tripleE by blast
        with H  show ?case
          by (simp add: disj_def)
      next
        assume asm2:"holds_forall_hyper I (lnot_hyper bs) (?Ss n)"
        have "(?Ss  n) = (?Ss (Suc n))"
          apply(simp only:eq)
          apply(rule)
          using asm2 jin
          apply(auto simp add:sem_rel_def map_comprehension_def sem_def if_then_else_skip_def if_then_else_def lnot_def holds_forall_hyper_def lnot_hyper_def)
          apply (metis SemSeq SemSkip SemAssume SemIf2 lnot_def snd_conv subsetD)
          by (metis in_mono snd_eqD)
        then show ?case using Suc asm2 by auto
      qed
    qed
  qed


  have un_jsexec_sound:"hyper_union (?Ss') = hyper_union (?after_n_finished)" unfolding hyper_union_def
    apply(rule)
  proof(rule)
    fix i
    have "\<And>n. \<exists>n'. (?Ss n) i = ((?after_n) n') i"
    proof -
      fix n
      show "\<exists>n'. (?Ss n) i = ((?after_n) n') i"
      proof(induction n)
        case 0
        have "(?Ss 0) i = ((?after_n) 0) i"
          by (simp add: priority_JS_based_execution_base)
        then show ?case
          by blast
      next
        case (Suc n)
        from Suc obtain n' where H:"(?Ss n) i  = ((?after_n) n') i" by blast
        from priority_JS_based_execution_step_strong JS_nonempty obtain J' where eq:"?Ss (Suc n) = sem_rel [i \<mapsto> if_then_else_skip (bs i) (Cs i) | i \<in> J'] (?Ss n)"
                                                                           and jinJS:"J' \<in> JS n (?Ss n)" by blast
        have "i \<notin> J' \<or> i \<in> J'" by auto
        then show ?case 
        proof
          assume asm:"i \<notin> J'"
          have "(?Ss (Suc n)) i = (?Ss n) i"
            apply(simp only:eq)
            using asm
            by(auto simp add:map_comprehension_def sem_rel_def sem_def)
          with H have "(?Ss (Suc n)) i = ((?after_n) n') i" 
            by auto
          thus ?case 
            by auto
        next
          assume asm:"i \<in> J'"
          have "(?Ss (Suc n)) i = ((?after_n) (Suc n')) i" 
            apply(simp only:eq)
            apply(auto simp add:map_comprehension_def sem_rel_def sem_def)
            using asm H apply auto[1]
            using H apply auto[1]
            apply (metis Diff_iff Pow_iff insert_Diff insert_subset JS_subset jinJS)
            apply (metis Diff_iff Diff_insert_absorb Pow_iff JS_subset jinJS subset_Diff_insert)
            by (auto simp add: asm)
          thus ?case 
            by blast
        qed
      qed
    qed
    hence "\<And>n. \<exists>n'. sem_rel [i \<mapsto> Assume (lnot (bs i)) | i \<in> I] (?Ss n) i = sem_rel [i \<mapsto> Assume (lnot (bs i)) | i \<in> I] (?after_n n') i"
      by (metis (lifting) sem_rel_def)
    thus "(\<Union>n. sem_rel [i \<mapsto> Assume (lnot (bs i)) | i \<in> I] (?Ss n) i) \<subseteq> (\<Union>n. sem_rel [i \<mapsto> Assume (lnot (bs i)) | i \<in> I] (?after_n n) i)"
      by blast
  next
    fix i
    have "\<And>n. \<exists>n'. (?after_n n) i = (?Ss n') i"
    proof -
      fix n
      show "\<exists>n'. (?after_n n) i = (?Ss n') i"
      proof(induction n)
        case 0
        have "?after_n 0 i = ?Ss 0 i"
          by (simp add: priority_JS_based_execution_base)
        then show ?case
          by blast
      next
        case (Suc n)
        from this obtain n' where H:"(?after_n n) i = (?Ss n') i" by blast
        have "i\<notin>I \<or> i \<in> I" by auto
        then show ?case 
        proof 
          assume asm:"i \<notin> I"
          have "(?after_n (Suc n)) i = (?Ss n') i" 
            using asm H
            by(auto simp add:map_comprehension_def sem_rel_def sem_def)
          then show ?case by blast
        next 
          assume asm: "i \<in> I"
          from priority_JS_based_execution_step_strong JS_nonempty obtain J' where eq:"?Ss (Suc n) = sem_rel [i \<mapsto> if_then_else_skip (bs i) (Cs i) | i \<in> J'] (?Ss n)"
                                                                             and jinJS:"J' \<in> JS n (?Ss n)" by blast
          have H1:"(\<forall>i\<in>I. \<forall>n. (\<exists>n'\<ge>n. \<not>(holds_forall (lnot (bs i)) (?Ss n' i)) \<longrightarrow> (\<exists>J \<in> JS n' (?Ss n'). i\<in>J)))" 
          proof (intro allI ballI)
            fix i n
            assume "i\<in>I"
            from jsexec_ivq have "(Iv n (?Ss n) \<or> holds_forall_hyper I (lnot_hyper bs) (?Ss n))" by auto
            thus "(\<exists>n'\<ge>n. \<not>(holds_forall (lnot (bs i)) (?Ss n' i)) \<longrightarrow> (\<exists>J \<in> JS n' (?Ss n'). i\<in>J))"
            proof 
              assume "Iv n (?Ss n)"
              with \<open>i\<in>I\<close> assms(3) have "\<exists>n'\<ge>n. entails (Iv n') (\<lambda>S. holds_forall (lnot (bs i)) (S i) \<or> (\<exists>J\<in>{J \<in> Pow I. i \<in> J}. V J S))"
                unfolding disj_def disj_I_def by auto
              hence "\<exists>n'\<ge>n. entails (Iv n') (\<lambda>S. \<not> holds_forall (lnot (bs i)) (S i) \<longrightarrow> (\<exists>J\<in>Pow I. i \<in> J \<and> V J S))"
                by (smt (verit) entailsE entailsI mem_Collect_eq)
              from this obtain n' where "n'\<ge>n" and entn':"entails (Iv n') (\<lambda>S. \<not> holds_forall (lnot (bs i)) (S i) \<longrightarrow> (\<exists>J\<in>Pow I. i \<in> J \<and> V J S))" by blast
              from jsexec_ivq have "(Iv n' (?Ss n') \<or> holds_forall_hyper I (lnot_hyper bs) (?Ss n'))" by auto
              thus ?thesis 
              proof
                assume "Iv n' (?Ss n')"
                with entn' have "\<not> holds_forall (lnot (bs i)) ((?Ss n') i) \<longrightarrow> (\<exists>J\<in>Pow I. i \<in> J \<and> V J (?Ss n'))"
                  by (simp add: entails_def)
                moreover have "\<And>J. (J\<in>Pow I \<and> i \<in> J \<and> V J (?Ss n')) \<Longrightarrow> (J \<in> JS n' (?Ss n') \<and> i \<in> J)" 
                proof -
                  fix J
                  assume asm:"(J\<in>Pow I \<and> i \<in> J \<and> V J (?Ss n'))"
                  thus "(J \<in> JS n' (?Ss n') \<and> i \<in> J)" 
                    using JS_prop2 by auto
                qed
                ultimately show ?thesis
                  using \<open>n \<le> n'\<close> by auto
              next 
                assume "holds_forall_hyper I (lnot_hyper bs) (?Ss n')"
                hence "\<not> holds_forall (lnot (bs i)) (priority_JS_based_execution bs Cs S JS I n' i) \<longrightarrow> (\<exists>J\<in>JS n' (priority_JS_based_execution bs Cs S JS I n'). i \<in> J)"
                  unfolding holds_forall_hyper_def lnot_hyper_def holds_forall_def lnot_def
                  by (simp add: \<open>i \<in> I\<close>)
                thus ?thesis using \<open>n'\<ge>n\<close> by auto
              qed
            next
              assume "holds_forall_hyper I (lnot_hyper bs) (?Ss n)"
              hence "\<not> holds_forall (lnot (bs i)) (priority_JS_based_execution bs Cs S JS I n i) \<longrightarrow> (\<exists>J\<in>JS n (priority_JS_based_execution bs Cs S JS I n). i \<in> J)"
                using \<open>i\<in>I\<close> by(auto simp add:holds_forall_def lnot_def holds_forall_hyper_def lnot_hyper_def) 
              thus ?thesis by auto
            qed
          qed
          let ?executes = "(\<lambda>n'. \<lambda>i. \<lambda>JS. (\<exists>J' \<in> JS n' (?Ss n'). (i \<in> J') \<and> (?Ss (Suc n') = sem_rel [i \<mapsto> if_then_else_skip (bs i) (Cs i) | i \<in> J'] (?Ss n'))))"
          from H1 all_q_revisited[of I bs Cs S JS] all_programs_reexecuted_or_dead[of I bs Cs S JS] JS_nonempty \<open>I \<noteq> {}\<close>
              have "\<forall>n. \<forall>i\<in>I. (holds_forall (lnot (bs i)) ((?Ss n) i)) 
            \<or> (\<exists>n' \<ge> n. ?executes n' i JS)" by (smt (z3))  
          hence "(holds_forall (lnot (bs i)) ((?Ss  n') i) 
                  \<or> (\<exists>n'' \<ge> n'. ?executes n'' i JS))"
            by (simp add: asm)
          then show ?case 
          proof 
            assume "(holds_forall (lnot (bs i)) ((?Ss n') i))"
            with H have "(holds_forall (lnot (bs i)) ((?after_n n) i))"
              by simp
            from this have "((?after_n (Suc n)) i) = ((?after_n n) i)" 
              apply(auto simp add:holds_forall_def lnot_def sem_rel_def map_comprehension_def sem_def if_then_else_skip_def if_then_else_def)
              by (metis SemSkip SemSeq SemAssume SemIf2 lnot_def snd_conv)
            with H show ?case
              by auto
          next
            assume "(\<exists>n'' \<ge> n'. ?executes n'' i JS)"
            hence "\<exists>n''::nat \<ge> n'. (?executes n'' i JS) \<and> (\<forall>n'''::nat< n''. n'''\<ge> n' \<longrightarrow> \<not>(?executes n''' i JS))"
              using least_one_exists[where ?P = "\<lambda>n''. n''\<ge> n' \<and> (?executes n'' i JS)"] by blast
            from this obtain n'' where ns_ineq:"n'' \<ge> n'" and i_exec: "(?executes n'' i JS)" 
                                 and no_less:"(\<forall>n'''::nat< n''. n'''\<ge> n' \<longrightarrow> \<not>(?executes n''' i JS))"
              using asm by auto
            have H2:"(\<forall>n'''\<le> n''. n'''> n' \<longrightarrow> (?Ss n''') i = (?Ss n') i)" 
            proof (intro allI impI)
              fix n'''
              assume asm1:"n''' \<le> n''"
              assume asm2:"n' < n'''"
              from asm1 asm2 show "(?Ss n''') i = (?Ss n') i"
              proof (induction n''')
                case 0
                then show ?case by auto
              next
                case (Suc n''')
                from priority_JS_based_execution_step_strong JS_nonempty obtain J'' where eq:"?Ss (Suc n''') = sem_rel [i \<mapsto> if_then_else_skip (bs i) (Cs i) | i \<in> J''] (?Ss n''')"
                                                                                   and jinJS:"J'' \<in> JS n''' (?Ss n''')" by blast
                from Suc no_less have H1:"\<not>(?executes n''' i JS)" 
                  by (simp add: less_eq_Suc_le)
                hence "i \<notin> J''"
                  using eq jinJS by auto
                from Suc have H2:"(?Ss n''') i = (?Ss n') i"
                  using not_less_less_Suc_eq by auto
                show ?case 
                  apply(simp only:eq)
                  apply(auto simp add:sem_rel_def map_comprehension_def)
                  using H2 \<open>i \<notin> J''\<close>
                  by(auto simp add: jinJS)
              qed
            qed
            from i_exec obtain J'' where "J''\<in>JS n'' (priority_JS_based_execution bs Cs S JS I n'')"
                                      and iinJ'':"i \<in> J''"
                                      and eq:"?Ss (Suc n'') = sem_rel [i \<mapsto> if_then_else_skip (bs i) (Cs i) | i \<in> J''] (?Ss n'')"
              by blast
            have "(?after_n (Suc n)) i = (?Ss (Suc n'')) i"
              apply(simp only:eq)
              using asm H H2 iinJ''
              apply(auto simp add:sem_rel_def map_comprehension_def)
              using ns_ineq apply auto[1]
              using ns_ineq by auto[1]
            then show ?case
              by blast
          qed
        qed
      qed
    qed
    hence "\<And>n. \<exists>n'. sem_rel [i \<mapsto> Assume (lnot (bs i)) | i \<in> I] (?after_n n) i = sem_rel [i \<mapsto> Assume (lnot (bs i)) | i \<in> I] (?Ss n') i" 
      by (metis (lifting) sem_rel_def)
    thus "(\<Union>n. sem_rel [i \<mapsto> Assume (lnot (bs i)) | i \<in> I] (?after_n n) i) \<subseteq> (\<Union>n. sem_rel [i \<mapsto> Assume (lnot (bs i)) | i \<in> I] (?Ss  n) i)" 
      by blast
  qed
 
  have wh_un_ss: "sem_rel [ i \<mapsto> While (Assume (bs i) ;; Cs i) | i \<in> I ] S = hyper_union (?after_n )"
    apply(rule)
    apply(auto simp add:sem_rel_def map_comprehension_def hyper_union_def)
       prefer 3
    apply (metis sem_lifted_after_n_steps.simps(1))
      prefer 3
    subgoal premises prems for x a b xa 
      using prems
    proof (induction xa)
      case 0
      then show ?thesis
        using prems(2) by auto
    next
      case (Suc nat)
      have "?after_n (Suc nat) x = ?after_n (nat) x"
        using Suc
        by(auto simp add:sem_rel_def map_comprehension_def)
      then show ?thesis
        using Suc.IH Suc.prems(2) prems(1) by auto
    qed
     apply(auto simp add:sem_def while_cond_def)
  proof -
    fix i l \<sigma>' \<sigma>
    assume asm1:"i\<in>I"
    assume asm2:"(l,\<sigma>) \<in> S i"
    assume asm3:"\<langle>While (Assume (bs i) ;; Cs i), \<sigma>\<rangle> \<rightarrow> \<sigma>'"
    from asm3 asm1 asm2 show "\<exists>n. (l, \<sigma>') \<in> ?after_n n i"
    proof (induction "While (Assume (bs i) ;; Cs i)" "\<sigma>" "\<sigma>'" arbitrary: S rule:single_sem.induct)
      case (SemWhileIter \<sigma> \<sigma>' \<sigma>'')
      have H1:"(l, \<sigma>') \<in> sem_lifted_after_n_steps bs Cs S I (Suc 0) i" 
        using \<open>i \<in> I\<close> \<open>\<langle>Assume (bs i) ;; Cs i, \<sigma>\<rangle> \<rightarrow> \<sigma>'\<close>
        apply(auto simp add:sem_rel_def map_comprehension_def sem_def if_then_else_skip_def if_then_else_def lnot_def)
        by (meson SemIf1 SemWhileIter.hyps(1) SemWhileIter.prems(2))
      have H2:"\<And>n n' s. s \<in> sem_lifted_after_n_steps bs Cs (sem_lifted_after_n_steps bs Cs S I (Suc 0)) I n i 
              \<longrightarrow> s \<in> sem_lifted_after_n_steps bs Cs S I (Suc n) i" 
        using \<open>i \<in> I\<close>
        apply(auto simp add:sem_rel_def map_comprehension_def)
      proof -
        fix n a b
        assume asm1: "i \<in> I"
        assume asm2: "(a, b) \<in> sem_lifted_after_n_steps bs Cs (sem_rel (\<lambda>i. if i \<in> I then Some (if_then_else_skip (bs i) (Cs i)) else None) S) I n i"
        from asm1 asm2 show "(a, b) \<in> sem (if_then_else_skip (bs i) (Cs i)) (sem_lifted_after_n_steps bs Cs S I n i)"
        proof (induction n arbitrary: b )
          case 0
          then show ?case 
            by(auto simp add:sem_rel_def)
        next
          case (Suc n)
          hence "(a, b) \<in> sem_lifted_after_n_steps bs Cs (sem_rel (\<lambda>i. if i \<in> I then Some (if_then_else_skip (bs i) (Cs i)) else None) S) I (Suc n) i" by auto
          from this show ?case 
            using Suc
            apply(auto simp add:sem_rel_def map_comprehension_def sem_def)
            by blast
        qed
      qed        
      from H1 H2 SemWhileIter have "\<exists>n. (l, \<sigma>'') \<in> sem_lifted_after_n_steps bs Cs S I (Suc n) i"
        by blast
      then show ?case
        by blast
    next
      case (SemWhileExit \<sigma>)
      then show ?case 
        by (metis sem_lifted_after_n_steps.simps(1))
    qed
  next
    fix i l \<sigma>' n
    assume asm1:"i\<in>I"
    assume asm2:"(l, \<sigma>') \<in> sem_lifted_after_n_steps bs Cs S I n i"
    from asm1 asm2 show "\<exists>\<sigma>. (l, \<sigma>) \<in> S i \<and> \<langle>While (Assume (bs i) ;; Cs i), \<sigma>\<rangle> \<rightarrow> \<sigma>'" 
    proof (induction n arbitrary: \<sigma>')
      case 0
      then show ?case
        using single_sem.SemWhileExit by auto
    next
      case (Suc n)
      have "\<And>C s s' s''. \<langle>While C, s\<rangle> \<rightarrow> s' \<and> \<langle>C,s'\<rangle> \<rightarrow> s'' \<Longrightarrow> \<langle>While C, s\<rangle> \<rightarrow> s''"
        using while_iter_reversed by auto
      obtain \<sigma>'' where "(l, \<sigma>'') \<in> sem_lifted_after_n_steps bs Cs S I n i" and ifte:"\<langle>if_then_else_skip (bs i) (Cs i), \<sigma>''\<rangle> \<rightarrow> \<sigma>'"
        using \<open>(l, \<sigma>') \<in> sem_lifted_after_n_steps bs Cs S I (Suc n) i\<close> \<open>i\<in>I\<close>
        by(auto simp add:sem_rel_def map_comprehension_def sem_def)
      with Suc obtain \<sigma> where \<sigma>_obt: "(l, \<sigma>) \<in> S i \<and> \<langle>While (Assume (bs i) ;; Cs i), \<sigma>\<rangle> \<rightarrow> \<sigma>''"
        by blast
     have H:"\<not> bs i \<sigma>'' \<Longrightarrow> \<sigma>'' = \<sigma>'"
       using ifte
       by(auto simp add:if_then_else_skip_def if_then_else_def)
     from ifte have "\<langle>(Assume (bs i) ;; Cs i), \<sigma>''\<rangle> \<rightarrow> \<sigma>' \<or> \<not> bs i \<sigma>''"
       by(auto simp add:if_then_else_skip_def if_then_else_def lnot_def)
     then show ?case 
     proof
       assume "\<langle>(Assume (bs i) ;; Cs i), \<sigma>''\<rangle> \<rightarrow> \<sigma>'"
       then show ?case using while_iter_reversed \<sigma>_obt
         by metis
     next
       assume "\<not> bs i \<sigma>''"
       hence "\<sigma>'' = \<sigma>'" using H by auto
       then show ?case using \<sigma>_obt by auto
     qed
    qed
  qed

  have wh_un: "sem_rel [ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ] S = hyper_union (?after_n_finished)" 
  proof(rule)
    fix i
    from wh_un_ss have H: "sem_rel [ i \<mapsto> While (Assume (bs i) ;; Cs i) | i \<in> I ] S i = hyper_union (?after_n) i" by auto
    show "sem_rel [ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ] S i = hyper_union (?after_n_finished) i"
    using H unfolding hyper_union_def while_cond_def 
    apply(auto simp add:sem_rel_def map_comprehension_def sem_def lnot_def set_eq_iff)
     apply (metis SemAssume lnot_def)
    by (metis SemAssume SemSeq lnot_def)
  qed
    
  have hasc_ss':"hyper_ascending I (?Ss')" 
  proof(intro hyper_ascendingI hyper_set_leI)
    fix n i
    assume "i\<in>I"
    from priority_JS_based_execution_step obtain J' where eq:"?Ss (Suc n) = sem_rel [i \<mapsto> if_then_else_skip (bs i) (Cs i) | i \<in> J'] (?Ss n)"
      by blast
    show "sem_rel (map_comprehension (\<lambda>i. Assume (lnot (bs i))) (\<lambda>i. i \<in> I)) (priority_JS_based_execution bs Cs S JS I n) i
           \<subseteq> sem_rel (map_comprehension (\<lambda>i. Assume (lnot (bs i))) (\<lambda>i. i \<in> I)) (priority_JS_based_execution bs Cs S JS I (Suc n)) i"
      using \<open>i \<in> I\<close>
      apply(simp only:eq)
      apply(auto simp add:sem_rel_def sem_def map_comprehension_def lnot_def if_then_else_skip_def if_then_else_def)
      by (metis SemSkip SemSeq SemAssume SemIf2 lnot_def)
  next
    fix n i
    assume "i \<notin> I"
    from priority_JS_based_execution_step_strong JS_nonempty obtain J' where eq:"?Ss (Suc n) = sem_rel [i \<mapsto> if_then_else_skip (bs i) (Cs i) | i \<in> J'] (?Ss n)"
                                                                          and jinJS:"J' \<in> JS n (?Ss n)"
      by blast
    from \<open>i\<notin>I\<close> priority_picker_inJS JS_nonempty
    show "sem_rel (map_comprehension (\<lambda>i. Assume (lnot (bs i))) (\<lambda>i. i \<in> I)) (priority_JS_based_execution bs Cs S JS I n) i =
           sem_rel (map_comprehension (\<lambda>i. Assume (lnot (bs i))) (\<lambda>i. i \<in> I)) (priority_JS_based_execution bs Cs S JS I (Suc n)) i"
      using \<open>i \<notin> I\<close> 
      apply(simp only:eq)
      using jinJS JS_subset[of "n" "(?Ss n)"] \<open>i \<notin> I\<close>
      by(auto simp add:sem_rel_def map_comprehension_def sem_def)
  qed

  from jsexec_ivq hasc_ss' assms(5) have qinf_un: "Q_inf (hyper_union (?Ss'))" 
    unfolding relational_upwards_closed_def by simp

  have hfa_wh: "(holds_forall_hyper I (lnot_hyper bs)) (sem_rel [ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ] S)" 
    unfolding while_cond_def
  by(auto simp add:sem_rel_def holds_forall_hyper_def lnot_hyper_def lnot_def map_comprehension_def sem_def)

  from wh_un un_jsexec_sound qinf_un hfa_wh show "(conj Q_inf (holds_forall_hyper I (lnot_hyper bs))) (sem_rel [ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ] S)"
    by (simp add: conj_def)
qed


subsection\<open>A partially synchronous version of the rule\<close>

abbreviation progress_side_condition1_sync where
"progress_side_condition1_sync Iv I bs V \<equiv> \<forall>n. entails (Iv n) (disj (disj_I (Pow I - {{}}) (\<lambda>J. conj (holds_forall_hyper J bs) (V J))) (holds_forall_hyper I (lnot_hyper bs)))"

abbreviation progress_side_condition2_sync where
"progress_side_condition2_sync Iv I bs V \<equiv> \<forall>n::nat. \<forall>i\<in>I. \<exists>n'\<ge>n. (entails (Iv n') (disj (\<lambda>S. (holds_forall (lnot (bs i)) (S i))) (disj_I ({J . J \<in> Pow I \<and> i \<in> J}) (\<lambda>J. conj (holds_forall_hyper J bs) (V J)))))" 

corollary while_nonfixed_lck_sync:
  assumes   "\<forall>n. \<forall>J\<in>(Pow I - {{}}). \<Turnstile> { conj (Iv n) (conj (holds_forall_hyper J bs) (V J))} [[i \<mapsto> Cs i | i \<in> J]] { Iv (Suc n) }"
      and   "progress_side_condition1_sync Iv I bs V"
      and   "progress_side_condition2_sync Iv I bs V"
      and   "\<forall>n. \<Turnstile> { (Iv n) } [[i \<mapsto> Assume (lnot (bs i)) | i \<in> I]] { Q }"
      and   "relational_upwards_closed I (\<lambda>n. Q) Q_inf"
      and   "I \<noteq> {}"
    shows   "\<Turnstile> { (Iv 0) } [[ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ]] { conj Q_inf (holds_forall_hyper I (lnot_hyper bs))}"
proof -
  let ?V' = "\<lambda>J. conj (holds_forall_hyper J bs) (V J)"
  have "\<forall>n. \<forall>J\<in>(Pow I - {{}}). \<Turnstile> { conj (Iv n) (?V' J)} [[i \<mapsto> if_then_else_skip (bs i) (Cs i) | i \<in> J]] { Iv (Suc n) }"
  proof (intro allI ballI relational_hyper_hoare_tripleI)
    fix n J S
    assume asm1: "J \<in> Pow I - {{}}"
    assume asm2: "Logic.conj (Iv n) (Logic.conj (holds_forall_hyper J bs) (V J)) S"
    with asm1 asm2 assms(1) have H:"Iv (Suc n) (sem_rel [i \<mapsto> Cs i | i \<in> J] S)" 
      unfolding relational_hyper_hoare_triple_def
      by blast
    have "(sem_rel [i \<mapsto> if_then_else_skip (bs i) (Cs i) | i \<in> J] S) = (sem_rel [i \<mapsto> Cs i | i \<in> J] S)"
      apply(rule)
      using asm2
      apply(auto simp add:sem_rel_def map_comprehension_def sem_def if_then_else_skip_def if_then_else_def lnot_def conj_def holds_forall_hyper_def holds_forall_hyper_def)
       apply fastforce
      by (metis SemAssume SemIf1 SemSeq snd_conv)
    with H show "Iv (Suc n) (sem_rel [i \<mapsto> if_then_else_skip (bs i) (Cs i) | i \<in> J] S)" by auto
  qed
  moreover have "progress_side_condition2 Iv I bs ?V'" using assms(3) by simp
  moreover have "progress_side_condition1 Iv I bs ?V'" using assms(2) by simp
  ultimately show ?thesis using assms while_nonfixed_lck[where ?V="?V'"] by auto
qed



subsection\<open>Further corollaries\<close>


lemma no_program_sem_lifted: 
  assumes "I = {}"
  shows "sem_rel [i \<mapsto> Cs i | i \<in> I] S = S"
  apply(rule)
  using assms
  by(auto simp add:sem_rel_def map_comprehension_def )


abbreviation progress_side_condition_simple where
"progress_side_condition_simple Iv I bs V \<equiv> entails Iv (\<lambda>S. (\<forall>i\<in>I. \<not>(holds_forall (lnot (bs i)) (S i)) \<longrightarrow> (\<exists>J\<in>(Pow I). i\<in>J \<and> (conj (holds_forall_hyper J bs) (V J) S))))"


lemma progress_simple_imp:
  assumes "progress_side_condition_simple Iv I bs V"
  shows "progress_side_condition1_sync (\<lambda>n. Iv) I bs V"
  using assms
  apply(auto simp add:entails_def holds_forall_def conj_def holds_forall_hyper_def holds_forall_hyper_def disj_def lnot_hyper_def)
  unfolding disj_I_def conj_def holds_forall_hyper_def
  by (metis Pow_bottom empty_iff insertE insert_Diff lnot_def snd_conv)



corollary while_nonfixed_lck_sync_simp:
  assumes   "\<forall>J\<in>(Pow I - {{}}). \<Turnstile> { conj Iv (conj (holds_forall_hyper J bs) (V J))} [[i \<mapsto> Cs i | i \<in> J]] { Iv }"
      and   "progress_side_condition_simple Iv I bs V"
      and   "\<Turnstile> { Iv } [[i \<mapsto> Assume (lnot (bs i)) | i \<in> I]] { Q }"
      and   "relational_upwards_closed I (\<lambda>n. Q) Q"
    shows   "\<Turnstile> { Iv } [[ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ]] { conj Q (holds_forall_hyper I (lnot_hyper bs))}"
proof -
  have "I = {} \<or> I \<noteq> {}"
    by auto
  thus ?thesis
  proof 
    assume "I = {}"
    show ?thesis
    proof (intro relational_hyper_hoare_tripleI)
      fix S
      assume "Iv S"
      have "(holds_forall_hyper I (lnot_hyper bs)) S"
        by(auto simp add:holds_forall_hyper_def lnot_hyper_def \<open>I = {}\<close>)
      from no_program_sem_lifted have "sem_rel [i \<mapsto> Assume (lnot (bs i)) | i \<in> I] S = S"
        using \<open>I = {}\<close> by auto
      with assms(3) have "Q S"
        by (metis \<open>Iv S\<close> relational_hyper_hoare_triple_def)
      from \<open>(holds_forall_hyper I (lnot_hyper bs)) S\<close> \<open>Q S\<close> have "(conj (holds_forall_hyper I (lnot_hyper bs)) Q) S" unfolding conj_def by auto
      with no_program_sem_lifted \<open>I = {}\<close> show "conj Q (holds_forall_hyper I (lnot_hyper bs)) (sem_rel (map_comprehension (\<lambda>i. while_cond (bs i) (Cs i)) (\<lambda>i. i \<in> I)) S)" 
        by (metis (full_types) conj_def)
    qed
  next
    assume asm: "I \<noteq> {}"
    let ?Iv' = "\<lambda>n::nat. Iv"
    from assms(1) have "\<And>n. \<forall>J\<in>(Pow I - {{}}). \<Turnstile> { conj (?Iv' n) (conj (holds_forall_hyper J bs) (V J))} [[i \<mapsto>  Cs i | i \<in> J]] { ?Iv' (Suc n) }"
      by simp
    moreover from assms(2) progress_simple_imp 
        have  "(progress_side_condition1_sync ?Iv' I bs V)" by auto
        moreover from assms(2) have "(progress_side_condition2_sync ?Iv' I bs V)"
          unfolding disj_def disj_I_def
          by (smt (verit, ccfv_threshold) entailsE entailsI mem_Collect_eq order_refl)
    moreover from assms(3) have "\<And>n. \<Turnstile> { (?Iv' n) } [[i \<mapsto> Assume (lnot (bs i)) | i \<in> I]] { Q }"
      by auto
    moreover from assms(4) have "relational_upwards_closed I (\<lambda>n. Q) Q" by blast
    ultimately show ?thesis using while_nonfixed_lck_sync[where Iv = "?Iv'" and ?I="I" and ?bs="bs" and ?V="V" and ?Cs="Cs" and ?Q="Q" and ?Q_inf = "Q"] asm
      by blast
  qed
qed


definition holds_for_prog where
"holds_for_prog j bs S \<longleftrightarrow> (\<forall>\<phi>\<in>(S j). (bs j) (snd \<phi>))"

abbreviation progress_side_condition_single where
"progress_side_condition_single Iv I bs U V \<equiv> entails Iv (\<lambda>S. (\<forall>i\<in>I. \<not>(holds_forall (lnot (bs i)) (S i)) \<longrightarrow> ((conj (holds_forall_hyper I bs) U) S) \<or> (conj (holds_for_prog i bs) (V i) S)))"


corollary while_nonfixed_lck_sync_single:
  assumes "\<Turnstile> { conj Iv (conj (holds_forall_hyper I bs) U)} [[i \<mapsto> Cs i | i \<in> I]] { Iv }" 
    and   "\<forall>j\<in>I. \<Turnstile> { conj Iv (conj (holds_for_prog j bs) (V j))} [[j \<mapsto> Cs j]] { Iv }"
    and   "(progress_side_condition_single Iv I bs U V)"
    and   "\<Turnstile> { Iv } [[i \<mapsto> Assume (lnot (bs i)) | i \<in> I]] { Q }"
    and   "relational_upwards_closed I (\<lambda>n. Q) Q"
    shows "\<Turnstile> { Iv } [[ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ]] { conj Q (holds_forall_hyper I (lnot_hyper bs))}"
proof - 
  have "card I = 1 \<or> card I \<noteq> 1" by auto
  thus ?thesis
  proof 
    assume asm0: "card I = 1"
    let ?V' = "\<lambda>J. disj (\<lambda>S. (\<forall>i\<in>J. V i S)) U"
    have "\<forall>J\<in>(Pow I - {{}}). \<Turnstile> { conj Iv (conj (holds_forall_hyper J bs) (?V' J))} [[i \<mapsto>  Cs i | i \<in> J]] { Iv }"
    proof (intro allI ballI)
      fix J
      assume asm: "J \<in> (Pow I - {{}})"
      with asm0 asm have "(\<exists>i. J = {i})"
        by (metis Diff_iff Pow_iff card_1_singletonE singleton_iff subset_singleton_iff)
      from this obtain j where asm2: "J = {j}" by auto
      have "j\<in>I"
        using asm asm2 by auto
      show "\<Turnstile> { conj Iv (conj (holds_forall_hyper J bs) (?V' J))} [[i \<mapsto>  Cs i | i \<in> J]] { Iv }"
      proof (intro relational_hyper_hoare_tripleI)
        fix S
        assume asm: "conj Iv (conj (holds_forall_hyper J bs) (?V' J)) S"
        hence "((\<forall>i\<in>J. V i S)) \<or> U S"
          by (simp add: conj_def disj_def)
        thus "Iv (sem_rel [i \<mapsto>  Cs i | i \<in> J] S) "
        proof
          assume "\<forall>i\<in>J. V i S"
          with asm2 have "V j S"
            by simp
          with asm have "conj Iv (conj (holds_for_prog j bs) (V j)) S"
            by (simp add: asm2 conj_def holds_for_prog_def holds_forall_hyper_def holds_forall_hyper_def)
          with assms(2) \<open>j\<in>I\<close> have "Iv (sem_rel [j \<mapsto> Cs j] S)"
            using relational_hyper_hoare_tripleE by blast
          moreover have "(sem_rel [j \<mapsto> Cs j] S) = sem_rel [i \<mapsto>  Cs i | i \<in> J] S"
            apply(rule) 
            using asm2 \<open>j\<in>I\<close>
            by(auto simp add:sem_rel_def map_comprehension_def)
          ultimately show ?thesis 
            by simp
        next
          assume "U S"
          with asm have "conj Iv (conj (holds_forall_hyper I bs) U) S"
            by (metis (lifting) \<open>j \<in> I\<close> asm0 asm2 card_1_singletonE conj_def empty_iff holds_forall_hyper_def insert_iff)
          with assms(1) have "Iv (sem_rel (map_comprehension Cs (\<lambda>i. i \<in> I)) S)"
            by (simp add: relational_hyper_hoare_triple_def)
          moreover have "(sem_rel (map_comprehension Cs (\<lambda>i. i \<in> I)) S) = (sem_rel (map_comprehension Cs (\<lambda>i. i \<in> J)) S)"
            apply(rule)
            using asm2 \<open>j\<in>I\<close>
            apply(auto simp add:sem_rel_def map_comprehension_def)
            using asm0 card_1_singletonE apply blast
            using asm0 card_1_singletonE by blast
          ultimately show ?thesis  by auto
        qed
      qed
    qed
    moreover have "(progress_side_condition_simple Iv I bs ?V')" 
      unfolding entails_def 
    proof (intro allI impI ballI)
      fix S i
      assume "Iv S" and "i\<in>I" and "\<not> holds_forall (lnot (bs i)) (S i)"
      with assms(3) have "((conj (holds_forall_hyper I bs) U) S) \<or> (conj (holds_for_prog i bs) (V i) S)"
        using entailsE by fastforce
      thus "\<exists>J\<in>Pow I. i \<in> J \<and> ((conj (holds_forall_hyper J bs) (?V' J)) S)"
      proof
        assume asm: "Logic.conj (holds_forall_hyper I bs) U S"
        thus ?thesis
          by (metis (mono_tags, lifting) Pow_top \<open>i \<in> I\<close> conj_def disj_def holds_forall_hyper_def)
      next
        assume asm4: "conj (holds_for_prog i bs) (V i) S"
        with \<open>i\<in>I\<close> have "{i}\<in>Pow I \<and> i \<in> {i}" 
          by simp
        from asm4 have "conj (holds_forall_hyper {i} bs) (?V' {i}) S" 
          by(auto simp add:conj_def holds_for_prog_def holds_forall_hyper_def holds_forall_hyper_def disj_def)
        thus ?thesis 
          using \<open>{i} \<in> Pow I \<and> i \<in> {i}\<close> by blast 
      qed
    qed
    ultimately show ?thesis using assms(4) assms(5) while_nonfixed_lck_sync_simp[where ?Iv = "Iv" and ?I="I" and ?bs="bs" and V="\<lambda>J. disj (\<lambda>S. (\<forall>i\<in>J. V i S)) U" and ?Cs="Cs" and ?Q="Q"]
      by blast
  next
    assume asm0: "card I \<noteq> 1"
    let ?V' = "\<lambda>J. if (J = I) then U else (if (card J = 1) then (\<lambda>S. (\<forall>i\<in>J. V i S)) else (\<lambda>S. False))"
    have "\<forall>J\<in>(Pow I - {{}}). \<Turnstile> { conj Iv (conj (holds_forall_hyper J bs) (?V' J))} [[i \<mapsto>  Cs i | i \<in> J]] { Iv }"
    proof (intro allI ballI)
      fix J
      assume asm: "J \<in> (Pow I - {{}})"
      with asm have "((J = I) \<or> (J \<noteq> I \<and> (\<exists>i. J = {i})) \<or> (J \<noteq> I \<and> (card J \<noteq> 1)))"
        by (meson card_1_singletonE)
      then show "\<Turnstile> { conj Iv (conj (holds_forall_hyper J bs) (?V' J))} [[i \<mapsto>  Cs i | i \<in> J]] { Iv }"
      proof (rule)
        assume asm1: "((J = I))"
        from asm1 have "conj Iv (conj (holds_forall_hyper J bs) (?V' J)) = conj Iv (conj (holds_forall_hyper I bs) U)"
          by (simp add: holds_forall_hyper_def)
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
          have "conj Iv (conj (holds_forall_hyper J bs) (?V' J)) = conj Iv (conj (holds_for_prog j bs) (V j))" using asm2
            by(auto simp add:holds_forall_hyper_def holds_for_prog_def asm2 conj_def holds_forall_hyper_def)
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
    moreover have "(progress_side_condition_simple Iv I bs ?V')" 
      unfolding entails_def 
    proof (intro allI impI ballI)
      fix S i
      assume "Iv S" and "i\<in>I" and "\<not> holds_forall (lnot (bs i)) (S i)"
      with assms(3) have "((conj (holds_forall_hyper I bs) U) S) \<or> (conj (holds_for_prog i bs) (V i) S)"
        using entailsE by fastforce
      thus "\<exists>J\<in>Pow I. i \<in> J \<and> ((conj (holds_forall_hyper J bs) (?V' J)) S)"
      proof
        assume asm: "Logic.conj (holds_forall_hyper I bs) U S"
        thus ?thesis
          by (smt (verit, ccfv_SIG) Pow_top \<open>i \<in> I\<close> holds_forall_hyper_def)
      next
        assume asm4: "conj (holds_for_prog i bs) (V i) S"
        with \<open>i\<in>I\<close> have "{i}\<in>Pow I \<and> i \<in> {i}" 
          by simp
        from asm4 have "conj (holds_forall_hyper {i} bs) (?V' {i}) S"
          using asm0
          by(auto simp add:conj_def holds_for_prog_def holds_forall_hyper_def holds_forall_hyper_def)
        thus ?thesis 
          using \<open>{i} \<in> Pow I \<and> i \<in> {i}\<close> by blast 
      qed
    qed
    ultimately show ?thesis using assms(4) assms(5) while_nonfixed_lck_sync_simp[where ?Iv = "Iv" and ?I="I" and ?bs="bs" and V="\<lambda>J. if J = I then U else (if (card J = 1) then (\<lambda>S. (\<forall>i\<in>J. V i S)) else (\<lambda>S. False))" and ?Cs="Cs" and ?Q="Q"]
      by blast
  qed
qed



text\<open>This is a weaker versions of while_sync_lck rule from the fixed alignment rules section. 
      However, now it is proven using solely while_nonfixed_lck_sync_simp.\<close>
corollary while_sync_lck_weaker:
  assumes "\<Turnstile> { conj Iv (holds_forall_hyper I bs) } [[i \<mapsto> (Cs i) | i \<in> I]] { conj Iv (low_exp_hyper I bs)}"
      and   "relational_upwards_closed I (\<lambda>n. disj Iv (hyper_emp I)) (disj Iv (hyper_emp I))"
    shows   "\<Turnstile> { conj Iv (low_exp_hyper I bs)} [[ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ]] { conj (disj Iv (hyper_emp I)) (holds_forall_hyper I (lnot_hyper bs))}"
proof -
  let ?V = "\<lambda>J. if J = I then (\<lambda>S. True) else (\<lambda>S. False)"
  let ?Iv = "conj Iv (low_exp_hyper I bs)"
  let ?Q = "disj Iv (hyper_emp I)"
  have H1: "\<forall>J\<in>(Pow I - {{}}). \<Turnstile> { conj ?Iv (conj (holds_forall_hyper J bs) (?V J))} [[i \<mapsto>  Cs i | i \<in> J]] { ?Iv }"
  proof (intro allI ballI impI relational_hyper_hoare_tripleI)
    fix J S
    assume asm: "conj ?Iv (conj (holds_forall_hyper J bs) (if J = I then (\<lambda>S. True) else (\<lambda>S. False))) S"
    have "J = I" 
    proof (rule ccontr)
      assume "J \<noteq> I"
      with asm show False
        by(auto simp add:conj_def)
    qed
    with asm assms(1) have "conj Iv (low_exp_hyper I bs) (sem_rel (map_comprehension Cs (\<lambda>i. i \<in> I)) S)"
      unfolding relational_hyper_hoare_triple_def conj_def
      by (simp add: holds_forall_hyper_def)
    moreover from \<open>J = I\<close> have "[i \<mapsto>  Cs i | i \<in> J] = (map_comprehension Cs (\<lambda>i. i \<in> I))"
      by(auto simp add:map_comprehension_def)
    ultimately show "?Iv (sem_rel [i \<mapsto>  Cs i | i \<in> J] S)"
      by (simp add: conj_def)
  qed
  have H2: "(progress_side_condition_simple ?Iv I bs ?V)"
    unfolding entails_def low_exp_hyper_def
    by (smt (verit, del_insts) Pow_top conj_def holds_forall_hyper_def holds_forall_def holds_forall_hyper_def lnot_def)
  have H3: "\<Turnstile> { ?Iv } [[i \<mapsto> Assume (lnot (bs i)) | i \<in> I]] { disj Iv (hyper_emp I) }" 
  proof (intro relational_hyper_hoare_tripleI)
    fix S
    assume "conj Iv (low_exp_hyper I bs) S"
    hence "Iv S" and "(low_exp_hyper I bs) S" 
      by (auto simp add: conj_def)
    hence "holds_forall_hyper I bs S \<or> holds_forall_hyper I (lnot_hyper bs) S "
      by (simp add: low_exp_either)
    thus "disj Iv (hyper_emp I) (sem_rel [i \<mapsto> Assume (lnot (bs i)) | i \<in> I] S)"
    proof
      assume asm: "holds_forall_hyper I bs S"
      have "(sem_rel [i \<mapsto> Assume (lnot (bs i)) | i \<in> I] S) = (\<lambda>i.(if (i\<in>I) then {} else S i))"
        apply(rule)
        using asm
        apply(auto simp add:holds_forall_hyper_def map_comprehension_def sem_rel_def sem_def lnot_def)
        by fastforce
      moreover have "(hyper_emp I) (\<lambda>i.(if (i\<in>I) then {} else S i))"
        by(auto simp add:hyper_emp_def)
      ultimately have "(hyper_emp I) (sem_rel [i \<mapsto> Assume (lnot (bs i)) | i \<in> I] S)" by auto
      thus ?thesis 
        by (simp add: disj_def)
    next
      assume asm: "holds_forall_hyper I (lnot_hyper bs) S"
      have "(sem_rel [i \<mapsto> Assume (lnot (bs i)) | i \<in> I] S) = S"
        apply(rule)
        using asm
        apply(auto simp add:sem_rel_def map_comprehension_def sem_def holds_forall_hyper_def lnot_hyper_def)
        by (metis SemAssume lnot_def sndI)
      with \<open>Iv S\<close> show ?thesis
        by (simp add: disj_def)
    qed
  qed
  show ?thesis
  proof (intro relational_hyper_hoare_tripleI)
    fix S
    assume "conj Iv (low_exp_hyper I bs) S"
    with H1 H2 H3 assms(2) while_nonfixed_lck_sync_simp[of "I" "?Iv" "bs"  "?V"  "Cs" "?Q"] 
      show "conj (disj Iv (hyper_emp I)) (holds_forall_hyper I (lnot_hyper bs)) (sem_rel [ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ] S)"
        by (simp add: relational_hyper_hoare_tripleE)
  qed
qed


lemma if_then_trueE:
  assumes "b \<sigma>" and "\<langle>if_then_else_skip b C, \<sigma>\<rangle> \<rightarrow> \<sigma>'"
  shows "\<langle>C, \<sigma>\<rangle> \<rightarrow> \<sigma>'"
  using assms
  unfolding if_then_else_skip_def if_then_else_def lnot_def
  by auto

lemma if_then_falseE:
  assumes "\<not> b \<sigma>" and "\<langle>if_then_else_skip b C, \<sigma>\<rangle> \<rightarrow> \<sigma>'"
  shows "\<sigma>' = \<sigma>"
  using assms
  unfolding if_then_else_skip_def if_then_else_def lnot_def
  by auto

lemma if_then_else_skip_falseE:
  assumes "\<not> b \<sigma>" and "\<langle>if_then_else_skip b C, \<sigma>\<rangle> \<rightarrow> \<sigma>'"
  shows "\<sigma>' = \<sigma>"
  using assms
  unfolding if_then_else_skip_def if_then_else_def lnot_def
  by auto

lemma repeat_with_if_false:
  assumes "\<not> b \<sigma>"
  shows "\<langle>repeat_with_if r b C, \<sigma>\<rangle> \<rightarrow> \<sigma>"
  using assms
proof (induction r)
  case 0
  show ?case by (simp add: SemSkip)
next
  case (Suc r)
  have "\<langle>if_then_else_skip b C, \<sigma>\<rangle> \<rightarrow> \<sigma>"
    using Suc.prems
    unfolding if_then_else_skip_def if_then_else_def lnot_def
    by (meson SemAssume SemIf2 SemSeq SemSkip)
  moreover have "\<langle>repeat_with_if r b C, \<sigma>\<rangle> \<rightarrow> \<sigma>"
    using Suc.IH Suc.prems by blast
  ultimately show ?case
    by (simp add: SemSeq)
qed

lemma repeat_with_if_false_only:
  assumes "\<not> b \<sigma>" and "\<langle>repeat_with_if r b C, \<sigma>\<rangle> \<rightarrow> \<sigma>'"
  shows "\<sigma>' = \<sigma>"
  using assms
proof (induction r arbitrary: \<sigma>')
  case 0
  then show ?case by auto
next
  case (Suc r)
  then obtain \<tau> where
    H1: "\<langle>if_then_else_skip b C, \<sigma>\<rangle> \<rightarrow> \<tau>"
    and H2: "\<langle>repeat_with_if r b C, \<tau>\<rangle> \<rightarrow> \<sigma>'"
    by auto
  from if_then_else_skip_falseE[OF Suc.prems(1) H1] have "\<tau> = \<sigma>" .
   show ?case
    using H2 Suc.IH \<open>\<tau> = \<sigma>\<close> assms(1) by blast
qed



lemma if_repeat_id: "sem (if_then_else_skip b (repeat_with_if r b C)) = sem (repeat_with_if r b C)"
proof (rule ext)
  fix S
  show "sem (if_then_else_skip b (repeat_with_if r b C)) S = sem (repeat_with_if r b C) S"
  proof (auto simp: sem_def)
    fix l \<sigma> \<sigma>'
    assume HS: "(l, \<sigma>) \<in> S"
       and H:  "\<langle>if_then_else_skip b (repeat_with_if r b C), \<sigma>\<rangle> \<rightarrow> \<sigma>'"
    show "\<exists>\<sigma>0. (l, \<sigma>0) \<in> S \<and> \<langle>repeat_with_if r b C, \<sigma>0\<rangle> \<rightarrow> \<sigma>'"
    proof (cases "b \<sigma>")
      case True
      from if_then_trueE[OF True H] have "\<langle>repeat_with_if r b C, \<sigma>\<rangle> \<rightarrow> \<sigma>'" .
      with HS show ?thesis by blast
    next
      case False
      from if_then_falseE[OF False H] have "\<sigma>' = \<sigma>" .
      moreover from repeat_with_if_false
      have "\<langle>repeat_with_if r b C, \<sigma>\<rangle> \<rightarrow> \<sigma>" 
        using False by blast
      ultimately show ?thesis using HS by blast
    qed
  next
    fix l \<sigma> \<sigma>'
    assume HS: "(l, \<sigma>) \<in> S"
       and H:  "\<langle>repeat_with_if r b C, \<sigma>\<rangle> \<rightarrow> \<sigma>'"
    show "\<exists>\<sigma>0. (l, \<sigma>0) \<in> S \<and> \<langle>if_then_else_skip b (repeat_with_if r b C), \<sigma>0\<rangle> \<rightarrow> \<sigma>'"
    proof (cases "b \<sigma>")
      case True
      have "\<langle>Assume b ;; repeat_with_if r b C, \<sigma>\<rangle> \<rightarrow> \<sigma>'"
        using True H by (meson SemAssume SemSeq)
      hence "\<langle>if_then_else_skip b (repeat_with_if r b C), \<sigma>\<rangle> \<rightarrow> \<sigma>'"
        unfolding if_then_else_skip_def if_then_else_def by (rule SemIf1)
      with HS show ?thesis by blast
    next
      case False
      from repeat_with_if_false_only[OF False H] have "\<sigma>' = \<sigma>" .
      hence "\<langle>Assume (lnot b), \<sigma>\<rangle> \<rightarrow> \<sigma>'"
        using False unfolding lnot_def by (auto intro: SemAssume)
      hence "\<langle>if_then_else_skip b (repeat_with_if r b C), \<sigma>\<rangle> \<rightarrow> \<sigma>'"
        unfolding if_then_else_skip_def if_then_else_def
        by (simp add: SemIf2 SemSeq SemSkip)
      with HS show ?thesis by blast
    qed
  qed
qed

text\<open>An asynchronous version of the while_fixed_lck rule from the fixed alignment rules section. 
      It is also a corollary of the while_nonfixed_lck rule.\<close>
corollary while_fixed_lck_async:
  assumes "\<Turnstile> { Iv } [[i \<mapsto> repeat_with_if (rf i) (bs i) (Cs i) | i \<in> I]] { Iv }" 
    and   "(\<forall>i\<in>I. (rf i) > 0)"
    and   "\<Turnstile> { Iv } [[i \<mapsto> Assume (lnot (bs i)) | i \<in> I]] { Q }"
    and   "relational_upwards_closed I (\<lambda>n. Q) Q_inf"
    and   "I \<noteq> {}"
    shows "\<Turnstile> { Iv } [[ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ]] { conj Q_inf (holds_forall_hyper I (lnot_hyper bs))}"
proof -
  let ?V = "\<lambda>J. if J = I then (\<lambda>S. True) else (\<lambda>S. False)"
  let ?Iv2 = "\<lambda>n. Iv"
  let ?Cs2 = "\<lambda>i. repeat_with_if (rf i) (bs i) (Cs i)"
  have "\<And>S. sem_rel [i \<mapsto> repeat_with_if (rf i) (bs i) (Cs i) | i \<in> I] S = sem_rel [i \<mapsto> if_then_else_skip (bs i) (repeat_with_if (rf i) (bs i) (Cs i)) | i \<in> I] S"
    apply(rule)
    apply(auto simp add:sem_rel_def map_comprehension_def) using if_repeat_id assms(2)
     apply metis
    by (simp add: assms(2) if_repeat_id)
  with assms(1) have H:"\<Turnstile> { Iv } [[i \<mapsto> if_then_else_skip (bs i) (repeat_with_if (rf i) (bs i) (Cs i)) | i \<in> I]] { Iv }"
    by (meson rewrite_rule_cond sem_equiv_hyper_cond_def)
  have "\<forall>n. \<forall>J\<in>(Pow I - {{}}). \<Turnstile> { conj (?Iv2 n) (?V J)} [[i \<mapsto> if_then_else_skip (bs i) (?Cs2 i) | i \<in> J]] { ?Iv2 (Suc n) }"
  proof (intro allI ballI)
    fix n J
    assume "J \<in> Pow I - {{}}"
    hence "J = I \<or> J \<noteq> I" by auto
    thus "\<Turnstile> { conj (?Iv2 n) (?V J)} [[i \<mapsto> if_then_else_skip (bs i) (?Cs2 i) | i \<in> J]] { ?Iv2 (Suc n) }"
    proof 
      assume asm:"J = I"
      show ?thesis 
        apply(simp only:asm)
        using H 
        using entail_conj_weaken cons_prec by blast
    next
      assume asm:"J \<noteq> I"
      show ?thesis using asm 
        by (simp add: conj_def relational_hyper_hoare_triple_def)
    qed
  qed
  moreover have "(progress_side_condition2 ?Iv2 I bs ?V)" 
    apply(intro allI entailsI ballI conjI impI entailsI)
  proof 
    fix n::nat
    fix i
    assume asm:"i \<in> I"
    show "n \<le> n  \<and>
            entails Iv
            (Logic.disj (\<lambda>S. holds_forall (lnot (bs i)) (S i))
              (disj_I {J \<in> Pow I. i \<in> J} (\<lambda>J. if J = I then \<lambda>S. True else (\<lambda>S. False))))"
      unfolding disj_def disj_I_def
      apply(auto)
      apply(intro entailsI) using asm by auto
  qed
  moreover have "(progress_side_condition1 ?Iv2 I bs ?V)" 
    apply(intro allI entailsI)
    by(auto simp add:disj_def disj_I_def holds_forall_hyper_def)
  ultimately have "\<Turnstile> { (?Iv2 0) } [[ i \<mapsto> (while_cond (bs i) (?Cs2 i)) | i \<in> I ]] { conj Q_inf (holds_forall_hyper I (lnot_hyper bs))}"
    using while_nonfixed_lck[of I ?Iv2 ?V bs ?Cs2 Q Q_inf] assms(3) assms(4) assms(5) 
    by blast
  with while_unfolded[of I rf bs Cs] assms(2) 
  show "\<Turnstile> { Iv } [[ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ]] { conj Q_inf (holds_forall_hyper I (lnot_hyper bs))}"
    apply(intro relational_hyper_hoare_tripleI)
    using relational_hyper_hoare_tripleE by fastforce
qed




subsection\<open>Notes for future generalization\<close>


text\<open>Generalizing J\<close>
(*
abbreviation progress_side_condition1G1 where
"progress_side_condition1G1 Iv I bs V \<equiv> \<forall>n. entails (Iv n) (disj (disj_I {J::nat\<Rightarrow>nat. (\<exists>i\<in>I. J i > 0)} (\<lambda>J. V J)) (holds_forall_hyper I (lnot_hyper bs)))"

abbreviation progress_side_condition2G1 where
"progress_side_condition2G1 Iv I bs V \<equiv> \<forall>n::nat. \<forall>i\<in>I. \<exists>n'\<ge>n. (entails (Iv n') (disj (\<lambda>S. (holds_forall (lnot (bs i)) (S i))) (disj_I {J::nat\<Rightarrow>nat . J i > 0} (\<lambda>J. V J))))"

theorem while_nonfixed_lckG1:
  assumes   "\<forall>n. \<forall>J::nat\<Rightarrow>nat. (\<exists>i\<in>I. J i > 0) \<longrightarrow>  \<Turnstile> { conj (Iv n) (V J)} [[i \<mapsto>  repeat_with_if (J i) (bs i) (Cs i) | i \<in> I]] { Iv (Suc n) }"
      and   "progress_side_condition1G1 Iv I bs V"
      and   "progress_side_condition2G1 Iv I bs V"
      and   "\<forall>n. \<Turnstile> { (Iv n) } [[i \<mapsto> Assume (lnot (bs i)) | i \<in> I]] { Q }"
      and   "relational_upwards_closed I (\<lambda>n. Q) Q_inf"
      and   "I \<noteq> {}"
    shows   "\<Turnstile> { (Iv 0) } [[ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ]] { conj Q_inf (holds_forall_hyper I (lnot_hyper bs))}"
*)



text\<open>Making V depend on n\<close>
(*
abbreviation progress_side_condition1G2 where
"progress_side_condition1G2 Iv I bs V \<equiv> \<forall>n. entails (Iv n) (disj (disj_I (Pow I - {{}}) (\<lambda>J. V n J)) (holds_forall_hyper I (lnot_hyper bs)))"

abbreviation progress_side_condition2G2 where
"progress_side_condition2G2 Iv I bs V \<equiv> \<forall>n::nat. \<forall>i\<in>I. \<exists>n'\<ge>n. (entails (Iv n') (disj (\<lambda>S. (holds_forall (lnot (bs i)) (S i))) (disj_I ({J . J \<in> Pow I \<and> i \<in> J}) (\<lambda>J. V n' J))))" 

theorem while_nonfixed_lckG2:
  assumes   "\<forall>n. \<forall>J\<in>(Pow I - {{}}). \<Turnstile> { conj (Iv n) (V n J)} [[i \<mapsto> if_then_else_skip (bs i) (Cs i) | i \<in> J]] { Iv (Suc n) }"
      and   "progress_side_condition1G2 Iv I bs V"
      and   "progress_side_condition2G2 Iv I bs V"
      and   "\<forall>n. \<Turnstile> { (Iv n) } [[i \<mapsto> Assume (lnot (bs i)) | i \<in> I]] { Q }"
      and   "relational_upwards_closed I (\<lambda>n. Q) Q_inf"
      and   "I \<noteq> {}"
    shows   "\<Turnstile> { (Iv 0) } [[ i \<mapsto> (while_cond (bs i) (Cs i)) | i \<in> I ]] { conj Q_inf (holds_forall_hyper I (lnot_hyper bs))}"
*)








section\<open>3.7 Refinement rules\<close>

subsection\<open>Meta refinement rule\<close>

text\<open>Refinement relation between two hyper-programs. Satisfied if all corresponding programs
      are in the refinement relation.\<close>
definition refines_hyper_program :: "'a hyper_program \<Rightarrow> 'a hyper_program \<Rightarrow> bool"where
"refines_hyper_program Cs1 Cs2  = (\<forall>S. (\<forall>i. (sem_rel Cs1 S) i \<subseteq> (sem_rel Cs2 S) i))"


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
      and "sat_assertion vals states Q (sem_rel Cs2 S)"
    shows "sat_assertion vals states Q (sem_rel Cs1 S)"
proof -
  from assms(2) assms(3) show "sat_assertion vals states Q (sem_rel Cs1 S)"
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

text\<open>Uses meta-level reasoning about refinement as compared to the refinement_rule below.\<close>
theorem meta_refinement_rule:
  assumes "refines_hyper_program Cs1 Cs2"
      and "\<Turnstile> {P} [Cs2] {interp_assert Q}"
      and "no_exists_state Q"
    shows "\<Turnstile> {P} [Cs1] {interp_assert Q}"
proof (rule relational_hyper_hoare_tripleI)
  fix S
  assume "P S"
  with assms(2) have "interp_assert Q (sem_rel Cs2 S)"
    by (simp add: relational_hyper_hoare_tripleE)
  with assms(1) assms(3) meta_refinement_rule_main show "interp_assert Q (sem_rel Cs1 S)" by blast
qed


definition sem_equiv_hyper where
"sem_equiv_hyper Cs1 Cs2 = (\<forall>S. (sem_rel Cs1 S) = (sem_rel Cs2 S))"

lemma ref_equiv: "sem_equiv_hyper Cs1 Cs2 \<longleftrightarrow> (refines_hyper_program Cs1 Cs2) \<and> (refines_hyper_program Cs2 Cs1)"
  unfolding sem_equiv_hyper_def refines_hyper_program_def
  by fastforce

definition refines_hyper_program_cond :: "'a hyper_program \<Rightarrow> 'a hyper_program \<Rightarrow> 'a rel_hyper_assertion \<Rightarrow> bool"where
"refines_hyper_program_cond Cs1 Cs2 P  = (\<forall>S. (P S) \<longrightarrow> (\<forall>i. (sem_rel Cs1 S) i \<subseteq> (sem_rel Cs2 S) i))"

lemma ref_equiv_cond: "sem_equiv_hyper_cond Cs1 Cs2 P \<longleftrightarrow> (refines_hyper_program_cond Cs1 Cs2 P) \<and> (refines_hyper_program_cond Cs2 Cs1 P)"
  unfolding sem_equiv_hyper_cond_def refines_hyper_program_cond_def
  by fastforce

lemma sem_equiv_hyper_refl:
  "sem_equiv_hyper Cs1 Cs2 = sem_equiv_hyper Cs2 Cs1"
  unfolding sem_equiv_hyper_def by auto


theorem rewrite_rule:
    assumes "sem_equiv_hyper Cs1 Cs2"
        and "\<Turnstile> {P} [Cs1] {Q}"
      shows "\<Turnstile> {P} [Cs2] {Q}"
  using assms
  by(auto simp add:relational_hyper_hoare_triple_def sem_rel_def sem_equiv_hyper_def)


subsection\<open>Semantic refinement rule\<close>

definition ref_cond where
 "ref_cond i j S = (\<forall>\<sigma>i\<in>(S i). \<exists>\<sigma>j \<in> (S j). \<sigma>i = \<sigma>j)"


lemma refinement_rule_main:
  assumes "\<Turnstile> {ref_cond 0 1} [[0 \<mapsto> C1, 1 \<mapsto> C2]] {ref_cond 0 1}"
  shows "refines_hyper_program [0 \<mapsto> C1] [0 \<mapsto> C2]"
  unfolding refines_hyper_program_def
proof (intro allI ballI)
  fix Ss::"'a hyper_set"
  fix i
  let ?Ss' = "(\<lambda>i. if i = 0 then (Ss 0) else (if i = 1 then (Ss 0) else {}))" 
  have "(ref_cond 0 1) ?Ss'" unfolding ref_cond_def by auto
  with assms have "(ref_cond 0 1) (sem_rel [0 \<mapsto> C1, 1 \<mapsto> C2] ?Ss')"
    by (simp add: relational_hyper_hoare_triple_def ref_cond_def)
  from this show "sem_rel [0 \<mapsto> C1] Ss i \<subseteq> sem_rel [0 \<mapsto> C2] Ss i" unfolding ref_cond_def 
    by(auto simp add:sem_rel_def)
qed


text\<open>Rule inspired by the wp-refine rule of LHC but instead of meta-level reasoning leverages RHHL's
      capability of proving the refinement result within the logic.\<close>
theorem refinement_rule:
  assumes "\<Turnstile> {ref_cond 0 1} [[0 \<mapsto> C1, 1 \<mapsto> C2]] {ref_cond 0 1}"
      and "\<Turnstile> {P} [[0 \<mapsto> C2]] {interp_assert Q}"
      and "no_exists_state Q"
    shows "\<Turnstile> {P} [[0 \<mapsto> C1]] {interp_assert Q}"
proof -
  from assms refinement_rule_main meta_refinement_rule show ?thesis by blast
qed



subsection\<open>Syntactic refinement rule\<close>

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
  with assms have H: "(refinement_assert 0 1 C1 C2) (sem_rel [0 \<mapsto> (interp_syn_stmt C1), 1 \<mapsto> (interp_syn_stmt C2)] ?S)"
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
  with H asm show "\<langle>interp_syn_stmt C2, \<sigma>\<rangle> \<rightarrow> \<sigma>'" by(auto simp add:refinement_assert_def sem_rel_def sem_def)
qed


lemma refines_program_lifted:
  assumes "refines_program C1 C2"
  shows "refines_hyper_program [0 \<mapsto> C1] [0 \<mapsto> C2]"
  unfolding refines_hyper_program_def 
proof (intro allI)
  fix S i 
  from assms show "sem_rel [0 \<mapsto> C1] S i \<subseteq> sem_rel [0 \<mapsto> C2] S i" unfolding refines_program_def
    apply(auto simp add:sem_rel_def sem_def)
    by auto
qed

text\<open>RefinementS - Same as the refinement_rule but uses only syntactic relational hyper-assertions in the refinement relational hyper-triple.\<close>
theorem refinementS:
  assumes "\<Turnstile> {interp_assert (refinement_syn_assert 0 1 C1 C2)} [[0 \<mapsto> (interp_syn_stmt C1), 1 \<mapsto> (interp_syn_stmt C2)]] {interp_assert (refinement_syn_assert 0 1 C1 C2)}"
      and "\<Turnstile> {P} [[0 \<mapsto> (interp_syn_stmt C2)]] {interp_assert Q}"
      and "no_exists_state Q"
    shows "\<Turnstile> {P} [[0 \<mapsto> (interp_syn_stmt C1)]] {interp_assert Q}"
proof -
  from refinement_syn_assert_sound refinement_hyper_triple_sound refines_program_lifted assms meta_refinement_rule show ?thesis
    by (smt (verit, ccfv_threshold) relational_hyper_hoare_tripleE relational_hyper_hoare_tripleI)
qed








section \<open>Further rules proven\<close>

theorem conj_rule:
  assumes "\<Turnstile> {P1} [Cs] {Q1}"
      and "\<Turnstile> {P2} [Cs] {Q2}"
    shows "\<Turnstile> {conj P1 P2} [Cs] {conj Q1 Q2}"
proof (intro relational_hyper_hoare_tripleI)
  fix S
  assume "(conj P1 P2) S"
  from \<open>(conj P1 P2) S\<close> assms(1) have H1:"Q1 (sem_rel Cs S)"
    by (simp add: relational_hyper_hoare_tripleE conj_def)
  from \<open>(conj P1 P2) S\<close> assms(2) have H2:"Q2 (sem_rel Cs S)"
    by (simp add: relational_hyper_hoare_tripleE conj_def)
  show "conj Q1 Q2 (sem_rel Cs S)"
    by(auto simp add:conj_def H1 H2)
qed


theorem disj_rule:
  assumes "\<Turnstile> {P1} [Cs] {Q1}"
      and "\<Turnstile> {P2} [Cs] {Q2}"
    shows "\<Turnstile> {disj P1 P2} [Cs] {disj Q1 Q2}"
proof (intro relational_hyper_hoare_tripleI)
  fix S
  assume "disj P1 P2 S"
  with assms have "Q1 (sem_rel Cs S) \<or> Q2 (sem_rel Cs S)"
    unfolding disj_def relational_hyper_hoare_triple_def by auto
  thus "disj Q1 Q2 (sem_rel Cs S)" unfolding disj_def by auto
qed


corollary postcondition_conj:
  assumes "\<Turnstile> {P} [Cs] {Q1}"
      and "\<Turnstile> {P} [Cs] {Q2}"
    shows "\<Turnstile> {P} [Cs] {conj Q1 Q2}"
  apply(rule cons)
   apply(rule entail_conj)
    apply(rule entails_refl)
   apply(rule entails_refl)
  apply(rule conj_rule)
  using assms by auto

end