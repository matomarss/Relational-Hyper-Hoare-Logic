text \<open>5 Further case studies\<close>
theory FurtherCaseStudies
  imports ProofRules
begin


section \<open>5.1 Fixed alignment of loops\<close>

datatype int_and_list =
  IntV int ("#_")
| ListV "int list"

fun len :: "int_and_list \<Rightarrow> int_and_list" where
"len (ListV xs) = IntV (int(length xs))" |
"len _ = undefined"

fun at_ol :: "int_and_list \<Rightarrow> int_and_list \<Rightarrow> int_and_list" (infixl "!\<^sub>o" 100)  where
"at_ol (ListV xs) (IntV i) = (if (i \<ge> 0) then IntV (xs ! (nat i)) else undefined)" |
"at_ol _ _ = undefined"

fun plus_ol :: "int_and_list \<Rightarrow> int_and_list \<Rightarrow> int_and_list"  (infixl "+\<^sub>o" 65) where
  "plus_ol (IntV i) (IntV j) = IntV (i + j)"
| "plus_ol _ _ = undefined"

fun times_ol :: "int_and_list \<Rightarrow> int_and_list \<Rightarrow> int_and_list"  (infixl "*\<^sub>o" 65) where
  "times_ol (IntV i) (IntV j) = IntV (i * j)"
| "times_ol _ _ = undefined"

fun minus_ol :: "int_and_list \<Rightarrow> int_and_list \<Rightarrow> int_and_list"  (infixl "-\<^sub>o" 65) where
  "minus_ol (IntV i) (IntV j) = IntV (i - j)"
| "minus_ol _ _ = undefined"

fun mod_ol :: "int_and_list \<Rightarrow> int_and_list \<Rightarrow> int_and_list"  (infixl "mod\<^sub>o" 65) where
  "mod_ol (IntV i) (IntV j) = IntV (i mod j)"
| "mod_ol _ _ = undefined"

fun less_ol :: "int_and_list \<Rightarrow> int_and_list \<Rightarrow> bool"  (infix "<\<^sub>o" 50) where
  "(IntV i) <\<^sub>o (IntV j) = (i < j)"
| "_ <\<^sub>o _ = undefined"

fun gr_ol :: "int_and_list \<Rightarrow> int_and_list \<Rightarrow> bool"  (infix ">\<^sub>o" 50) where
  "(IntV i) >\<^sub>o (IntV j) = (i > j)"
| "_ >\<^sub>o _ = undefined"

fun lesseq_ol :: "int_and_list \<Rightarrow> int_and_list \<Rightarrow> bool"  (infix "\<le>\<^sub>o" 50) where
  "(IntV i) \<le>\<^sub>o (IntV j) = (i \<le> j)"
| "_ \<le>\<^sub>o _ = undefined"

fun greq_ol :: "int_and_list \<Rightarrow> int_and_list \<Rightarrow> bool"  (infix "\<ge>\<^sub>o" 50) where
  "(IntV i) \<ge>\<^sub>o (IntV j) = (i \<ge> j)"
| "_ \<ge>\<^sub>o _ = undefined"



abbreviation list_reduce :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat, int_and_list) stmt" where
"list_reduce s x i n \<equiv>
  x ::= (\<lambda>\<sigma>. #0);;
  i ::= (\<lambda>\<sigma>. #0);;
  n ::= (\<lambda>\<sigma>. len (\<sigma> s));;
  WHILE (\<lambda>\<sigma>. (\<sigma> i) <\<^sub>o (\<sigma> n)) DO (
    x ::= (\<lambda>\<sigma>. (\<sigma> x) +\<^sub>o (\<sigma> s) !\<^sub>o (\<sigma> i));;
    i ::= (\<lambda>\<sigma>. (\<sigma> i) +\<^sub>o #1)
  )
"


abbreviation list_reduce_optimized :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat, int_and_list) stmt" where
"list_reduce_optimized s x i n x0 x1 x2 x3 \<equiv> 
  x0 ::= (\<lambda>\<sigma>. #0);;
  x1 ::= (\<lambda>\<sigma>. #0);;
  x2 ::= (\<lambda>\<sigma>. #0);;
  x3 ::= (\<lambda>\<sigma>. #0);;
  i ::= (\<lambda>\<sigma>. #0);;
  n ::= (\<lambda>\<sigma>. len (\<sigma> s));;
  WHILE (\<lambda>\<sigma>. ((\<sigma> i) +\<^sub>o #3) <\<^sub>o (\<sigma> n)) DO(
    x0 ::= (\<lambda>\<sigma>. (\<sigma> x0) +\<^sub>o (\<sigma> s) !\<^sub>o (\<sigma> i));;
    x1 ::= (\<lambda>\<sigma>. (\<sigma> x1) +\<^sub>o (\<sigma> s) !\<^sub>o (\<sigma> i +\<^sub>o #1));;
    x2 ::= (\<lambda>\<sigma>. (\<sigma> x2) +\<^sub>o (\<sigma> s) !\<^sub>o (\<sigma> i +\<^sub>o #2));;
    x3 ::= (\<lambda>\<sigma>. (\<sigma> x3) +\<^sub>o (\<sigma> s) !\<^sub>o (\<sigma> i +\<^sub>o #3));;
    i ::= (\<lambda>\<sigma>. (\<sigma> i) +\<^sub>o #4)
  );;
  x ::= (\<lambda>\<sigma>. (\<sigma> x0) +\<^sub>o (\<sigma> x1) +\<^sub>o (\<sigma> x2) +\<^sub>o (\<sigma> x3))
"

text\<open>IMPORTANT: The invariant and most of the assertions contain additional typing formulas
                compared to the version presented in the report.
                This is because we implement a simple type-system and need to always keep around 
                the information about which variable is of what type. 
                We did not want to present this purely technical aspect of the proof.\<close>
proposition
  fixes s x i n x0 x1 x2 x3 :: nat
  assumes vars_distinct : "distinct [s, x, i, n, x0, x1, x2, x3]"
  shows "(\<Turnstile>  {(\<lambda>S::int_and_list hyper_set. 
                (\<forall>\<sigma>2 \<in> (S 2). \<exists>\<sigma>1 \<in> (S 1). (snd \<sigma>1 s) = (snd \<sigma>2 s)) 
              \<and> (\<forall>\<sigma>1 \<in> (S 1). \<exists>\<sigma>2 \<in> (S 2). (snd \<sigma>1 s) = (snd \<sigma>2 s))
              \<and> (\<forall>\<sigma>1 \<in> (S 1). \<forall>\<sigma>1' \<in> (S 1).(snd \<sigma>1 s) = (snd \<sigma>1' s)) 
              \<and> (\<forall>\<sigma>2 \<in> (S 2). \<forall>\<sigma>2' \<in> (S 2).(snd \<sigma>2 s) = (snd \<sigma>2' s))
              \<and> (\<forall>\<sigma>1 \<in> (S 1). len (snd \<sigma>1 s) mod\<^sub>o #4 = #0) 
              \<and> (\<forall>\<sigma>2 \<in> (S 2). len (snd \<sigma>2 s) mod\<^sub>o #4 = #0)
              \<and> (\<forall>\<sigma>1 \<in> (S 1). \<exists>xs::int list. (snd \<sigma>1 s) = (ListV xs)) \<and> (\<forall>\<sigma>2 \<in> (S 2). \<exists>xs::int list. (snd \<sigma>2 s) = (ListV xs)))}  
            [[1 \<mapsto> list_reduce s x i n, 2 \<mapsto> list_reduce_optimized s x i n x0 x1 x2 x3]::int_and_list hyper_program] 
             {(\<lambda>S::int_and_list hyper_set. \<forall>\<sigma>2 \<in> (S 2). \<exists>\<sigma>1 \<in> (S 1). (snd \<sigma>2 x) = (snd \<sigma>1 x))})"
proof -
  let ?bs = "(\<lambda>j. if (j=1) then (\<lambda>\<sigma>. (\<sigma> i) <\<^sub>o (\<sigma> n)) else (\<lambda>\<sigma>. ((\<sigma> i) +\<^sub>o #3) <\<^sub>o (\<sigma> n)))"
  let ?rf = "(\<lambda>j. if (j=1) then 4 else 1)"
  let ?P = "(\<lambda>S::int_and_list hyper_set. 
                (\<forall>\<sigma>2 \<in> (S 2). \<exists>\<sigma>1 \<in> (S 1). (snd \<sigma>1 s) = (snd \<sigma>2 s)) 
              \<and> (\<forall>\<sigma>1 \<in> (S 1). \<exists>\<sigma>2 \<in> (S 2). (snd \<sigma>1 s) = (snd \<sigma>2 s))
              \<and> (\<forall>\<sigma>1 \<in> (S 1). \<forall>\<sigma>1' \<in> (S 1).(snd \<sigma>1 s) = (snd \<sigma>1' s)) 
              \<and> (\<forall>\<sigma>2 \<in> (S 2). \<forall>\<sigma>2' \<in> (S 2).(snd \<sigma>2 s) = (snd \<sigma>2' s))
              \<and> (\<forall>\<sigma>1 \<in> (S 1). len (snd \<sigma>1 s) mod\<^sub>o #4 = #0) 
              \<and> (\<forall>\<sigma>2 \<in> (S 2). len (snd \<sigma>2 s) mod\<^sub>o #4 = #0)
              \<and> (\<forall>\<sigma>1 \<in> (S 1). \<exists>xs::int list. (snd \<sigma>1 s) = (ListV xs)) \<and> (\<forall>\<sigma>2 \<in> (S 2). \<exists>xs::int list. (snd \<sigma>2 s) = (ListV xs)))"
  let ?Iv = "(\<lambda>S::int_and_list hyper_set. 
                (\<forall>\<sigma>2 \<in> (S 2). \<exists>\<sigma>1 \<in> (S 1). 
                  (snd \<sigma>1 s) = (snd \<sigma>2 s) \<and>
                  (snd \<sigma>1 x) = (snd \<sigma>2 x0) +\<^sub>o (snd \<sigma>2 x1) +\<^sub>o (snd \<sigma>2 x2) +\<^sub>o (snd \<sigma>2 x3) \<and> 
                  (snd \<sigma>1 i) = (snd \<sigma>2 i)
                ) \<and>
                (\<forall>\<sigma>1 \<in> (S 1). \<exists>\<sigma>2 \<in> (S 2). 
                  (snd \<sigma>1 s) = (snd \<sigma>2 s) \<and>
                  (snd \<sigma>1 x) = (snd \<sigma>2 x0) +\<^sub>o (snd \<sigma>2 x1) +\<^sub>o (snd \<sigma>2 x2) +\<^sub>o (snd \<sigma>2 x3) \<and> 
                  (snd \<sigma>1 i) = (snd \<sigma>2 i)
                ) \<and>
                (\<forall>\<sigma>1 \<in> (S 1). \<forall>\<sigma>1' \<in> (S 1).(snd \<sigma>1 s) = (snd \<sigma>1' s) \<and> (snd \<sigma>1 i) = (snd \<sigma>1' i)) \<and> 
                (\<forall>\<sigma>2 \<in> (S 2). \<forall>\<sigma>2' \<in> (S 2).(snd \<sigma>2 s) = (snd \<sigma>2' s) \<and> (snd \<sigma>2 i) = (snd \<sigma>2' i)) \<and> 
                (\<forall>\<sigma>1 \<in> (S 1). (snd \<sigma>1 n) mod\<^sub>o #4 = #0) \<and> (\<forall>\<sigma>2 \<in> (S 2). (snd \<sigma>2 n) mod\<^sub>o #4 = #0) \<and>
                (\<forall>\<sigma>1 \<in> (S 1). (snd \<sigma>1 i) mod\<^sub>o #4 = #0) \<and> (\<forall>\<sigma>2 \<in> (S 2). (snd \<sigma>2 i) mod\<^sub>o #4 = #0) \<and>
                (\<forall>\<sigma>1 \<in> (S 1). snd \<sigma>1 n = len (snd \<sigma>1 s)) \<and>
                (\<forall>\<sigma>2 \<in> (S 2). snd \<sigma>2 n = len (snd \<sigma>2 s)) \<and>
                (\<forall>\<sigma>1 \<in> (S 1). snd \<sigma>1 i \<ge>\<^sub>o #0) \<and>
                (\<forall>\<sigma>2 \<in> (S 2). snd \<sigma>2 i \<ge>\<^sub>o #0) \<and>
               (\<forall>\<sigma>1 \<in> (S 1). \<exists>xs::int list. (snd \<sigma>1 s) = (ListV xs)) \<and> (\<forall>\<sigma>2 \<in> (S 2). \<exists>xs::int list. (snd \<sigma>2 s) = (ListV xs)) \<and>
               (\<forall>\<sigma>1 \<in> (S 1). \<exists>n'::int. (snd \<sigma>1 n) = (#n')) \<and> (\<forall>\<sigma>2 \<in> (S 2). \<exists>n'::int. (snd \<sigma>2 n) = (#n')) \<and>
               (\<forall>\<sigma>1 \<in> (S 1). \<exists>i'::int. (snd \<sigma>1 i) = (#i')) \<and> (\<forall>\<sigma>2 \<in> (S 2). \<exists>i'::int. (snd \<sigma>2 i) = (#i')) \<and>
               (\<forall>\<sigma>1 \<in> (S 1). \<exists>x'::int. (snd \<sigma>1 x) = (#x')) \<and> 
               (\<forall>\<sigma>2 \<in> (S 2). \<exists>x0'::int. (snd \<sigma>2 x0) = (#x0')) \<and> (\<forall>\<sigma>2 \<in> (S 2). \<exists>x1'::int. (snd \<sigma>2 x1) = (#x1')) \<and>
                (\<forall>\<sigma>2 \<in> (S 2). \<exists>x2'::int. (snd \<sigma>2 x2) = (#x2')) \<and> (\<forall>\<sigma>2 \<in> (S 2). \<exists>x3'::int. (snd \<sigma>2 x3) = (#x3'))
              )"
  let ?PC0 = "(\<lambda>S::int_and_list hyper_set. 
                (\<forall>\<sigma>2 \<in> (S 2). \<exists>\<sigma>1 \<in> (S 1). 
                  (snd \<sigma>1 s) = (snd \<sigma>2 s) \<and>
                  (snd \<sigma>1 x) = (snd \<sigma>2 x0) +\<^sub>o (snd \<sigma>2 x1) +\<^sub>o (snd \<sigma>2 x2) +\<^sub>o (snd \<sigma>2 x3) \<and> 
                  (snd \<sigma>1 i) = (snd \<sigma>2 i) +\<^sub>o #1
                ) \<and>
                (\<forall>\<sigma>1 \<in> (S 1). \<exists>\<sigma>2 \<in> (S 2). 
                  (snd \<sigma>1 s) = (snd \<sigma>2 s) \<and>
                  (snd \<sigma>1 x) = (snd \<sigma>2 x0) +\<^sub>o (snd \<sigma>2 x1) +\<^sub>o (snd \<sigma>2 x2) +\<^sub>o (snd \<sigma>2 x3) \<and> 
                  (snd \<sigma>1 i) = (snd \<sigma>2 i) +\<^sub>o #1
                ) \<and>
                (\<forall>\<sigma>1 \<in> (S 1). \<forall>\<sigma>1' \<in> (S 1).(snd \<sigma>1 s) = (snd \<sigma>1' s) \<and> (snd \<sigma>1 i) = (snd \<sigma>1' i)) \<and> 
                (\<forall>\<sigma>2 \<in> (S 2). \<forall>\<sigma>2' \<in> (S 2).(snd \<sigma>2 s) = (snd \<sigma>2' s) \<and> (snd \<sigma>2 i) = (snd \<sigma>2' i)) \<and> 
                (\<forall>\<sigma>1 \<in> (S 1). (snd \<sigma>1 n) mod\<^sub>o #4 = #0) \<and> (\<forall>\<sigma>2 \<in> (S 2). (snd \<sigma>2 n) mod\<^sub>o #4 = #0) \<and>
                (\<forall>\<sigma>1 \<in> (S 1). (snd \<sigma>1 i) mod\<^sub>o #4 = #1) \<and> (\<forall>\<sigma>2 \<in> (S 2). (snd \<sigma>2 i) mod\<^sub>o #4 = #0) \<and>
                (\<forall>\<sigma>1 \<in> (S 1). snd \<sigma>1 n = len (snd \<sigma>1 s)) \<and>
                (\<forall>\<sigma>2 \<in> (S 2). snd \<sigma>2 n = len (snd \<sigma>2 s)) \<and>
                (\<forall>\<sigma>1 \<in> (S 1). snd \<sigma>1 i \<ge>\<^sub>o #0) \<and>
                (\<forall>\<sigma>2 \<in> (S 2). snd \<sigma>2 i \<ge>\<^sub>o #0) \<and>
               (\<forall>\<sigma>1 \<in> (S 1). \<exists>xs::int list. (snd \<sigma>1 s) = (ListV xs)) \<and> (\<forall>\<sigma>2 \<in> (S 2). \<exists>xs::int list. (snd \<sigma>2 s) = (ListV xs)) \<and>
               (\<forall>\<sigma>1 \<in> (S 1). \<exists>n'::int. (snd \<sigma>1 n) = (#n')) \<and> (\<forall>\<sigma>2 \<in> (S 2). \<exists>n'::int. (snd \<sigma>2 n) = (#n')) \<and>
               (\<forall>\<sigma>1 \<in> (S 1). \<exists>i'::int. (snd \<sigma>1 i) = (#i')) \<and> (\<forall>\<sigma>2 \<in> (S 2). \<exists>i'::int. (snd \<sigma>2 i) = (#i')) \<and>
               (\<forall>\<sigma>1 \<in> (S 1). \<exists>x'::int. (snd \<sigma>1 x) = (#x')) \<and> 
               (\<forall>\<sigma>2 \<in> (S 2). \<exists>x0'::int. (snd \<sigma>2 x0) = (#x0')) \<and> (\<forall>\<sigma>2 \<in> (S 2). \<exists>x1'::int. (snd \<sigma>2 x1) = (#x1')) \<and>
                (\<forall>\<sigma>2 \<in> (S 2). \<exists>x2'::int. (snd \<sigma>2 x2) = (#x2')) \<and> (\<forall>\<sigma>2 \<in> (S 2). \<exists>x3'::int. (snd \<sigma>2 x3) = (#x3'))
                \<and> (holds_forall_hyper {1,2} ?bs S)
              )"

  let ?PC1 = "(\<lambda>S::int_and_list hyper_set. 
                (\<forall>\<sigma>2 \<in> (S 2). \<exists>\<sigma>1 \<in> (S 1). 
                  (snd \<sigma>1 s) = (snd \<sigma>2 s) \<and>
                  (snd \<sigma>1 x) = (snd \<sigma>2 x0) +\<^sub>o (snd \<sigma>2 x1) +\<^sub>o (snd \<sigma>2 x2) +\<^sub>o (snd \<sigma>2 x3) \<and> 
                  (snd \<sigma>1 i) = (snd \<sigma>2 i) +\<^sub>o #2
                ) \<and>
                (\<forall>\<sigma>1 \<in> (S 1). \<exists>\<sigma>2 \<in> (S 2). 
                  (snd \<sigma>1 s) = (snd \<sigma>2 s) \<and>
                  (snd \<sigma>1 x) = (snd \<sigma>2 x0) +\<^sub>o (snd \<sigma>2 x1) +\<^sub>o (snd \<sigma>2 x2) +\<^sub>o (snd \<sigma>2 x3) \<and> 
                  (snd \<sigma>1 i) = (snd \<sigma>2 i) +\<^sub>o #2
                ) \<and>
                (\<forall>\<sigma>1 \<in> (S 1). \<forall>\<sigma>1' \<in> (S 1).(snd \<sigma>1 s) = (snd \<sigma>1' s) \<and> (snd \<sigma>1 i) = (snd \<sigma>1' i)) \<and> 
                (\<forall>\<sigma>2 \<in> (S 2). \<forall>\<sigma>2' \<in> (S 2).(snd \<sigma>2 s) = (snd \<sigma>2' s) \<and> (snd \<sigma>2 i) = (snd \<sigma>2' i)) \<and> 
                (\<forall>\<sigma>1 \<in> (S 1). (snd \<sigma>1 n) mod\<^sub>o #4 = #0) \<and> (\<forall>\<sigma>2 \<in> (S 2). (snd \<sigma>2 n) mod\<^sub>o #4 = #0) \<and>
                (\<forall>\<sigma>1 \<in> (S 1). (snd \<sigma>1 i) mod\<^sub>o #4 = #2) \<and> (\<forall>\<sigma>2 \<in> (S 2). (snd \<sigma>2 i) mod\<^sub>o #4 = #0) \<and>
                (\<forall>\<sigma>1 \<in> (S 1). snd \<sigma>1 n = len (snd \<sigma>1 s)) \<and>
                (\<forall>\<sigma>2 \<in> (S 2). snd \<sigma>2 n = len (snd \<sigma>2 s)) \<and>
                (\<forall>\<sigma>1 \<in> (S 1). snd \<sigma>1 i \<ge>\<^sub>o #0) \<and>
                (\<forall>\<sigma>2 \<in> (S 2). snd \<sigma>2 i \<ge>\<^sub>o #0) \<and>
               (\<forall>\<sigma>1 \<in> (S 1). \<exists>xs::int list. (snd \<sigma>1 s) = (ListV xs)) \<and> (\<forall>\<sigma>2 \<in> (S 2). \<exists>xs::int list. (snd \<sigma>2 s) = (ListV xs)) \<and>
               (\<forall>\<sigma>1 \<in> (S 1). \<exists>n'::int. (snd \<sigma>1 n) = (#n')) \<and> (\<forall>\<sigma>2 \<in> (S 2). \<exists>n'::int. (snd \<sigma>2 n) = (#n')) \<and>
               (\<forall>\<sigma>1 \<in> (S 1). \<exists>i'::int. (snd \<sigma>1 i) = (#i')) \<and> (\<forall>\<sigma>2 \<in> (S 2). \<exists>i'::int. (snd \<sigma>2 i) = (#i')) \<and>
               (\<forall>\<sigma>1 \<in> (S 1). \<exists>x'::int. (snd \<sigma>1 x) = (#x')) \<and> 
               (\<forall>\<sigma>2 \<in> (S 2). \<exists>x0'::int. (snd \<sigma>2 x0) = (#x0')) \<and> (\<forall>\<sigma>2 \<in> (S 2). \<exists>x1'::int. (snd \<sigma>2 x1) = (#x1')) \<and>
                (\<forall>\<sigma>2 \<in> (S 2). \<exists>x2'::int. (snd \<sigma>2 x2) = (#x2')) \<and> (\<forall>\<sigma>2 \<in> (S 2). \<exists>x3'::int. (snd \<sigma>2 x3) = (#x3'))
                \<and> (holds_forall_hyper {1,2} ?bs S)
              )"

  let ?PC2 = "(\<lambda>S::int_and_list hyper_set. 
                (\<forall>\<sigma>2 \<in> (S 2). \<exists>\<sigma>1 \<in> (S 1). 
                  (snd \<sigma>1 s) = (snd \<sigma>2 s) \<and>
                  (snd \<sigma>1 x) = (snd \<sigma>2 x0) +\<^sub>o (snd \<sigma>2 x1) +\<^sub>o (snd \<sigma>2 x2) +\<^sub>o (snd \<sigma>2 x3) \<and> 
                  (snd \<sigma>1 i) = (snd \<sigma>2 i) +\<^sub>o #3
                ) \<and>
                (\<forall>\<sigma>1 \<in> (S 1). \<exists>\<sigma>2 \<in> (S 2). 
                  (snd \<sigma>1 s) = (snd \<sigma>2 s) \<and>
                  (snd \<sigma>1 x) = (snd \<sigma>2 x0) +\<^sub>o (snd \<sigma>2 x1) +\<^sub>o (snd \<sigma>2 x2) +\<^sub>o (snd \<sigma>2 x3) \<and> 
                  (snd \<sigma>1 i) = (snd \<sigma>2 i) +\<^sub>o #3
                ) \<and>
                (\<forall>\<sigma>1 \<in> (S 1). \<forall>\<sigma>1' \<in> (S 1).(snd \<sigma>1 s) = (snd \<sigma>1' s) \<and> (snd \<sigma>1 i) = (snd \<sigma>1' i)) \<and> 
                (\<forall>\<sigma>2 \<in> (S 2). \<forall>\<sigma>2' \<in> (S 2).(snd \<sigma>2 s) = (snd \<sigma>2' s) \<and> (snd \<sigma>2 i) = (snd \<sigma>2' i)) \<and> 
                (\<forall>\<sigma>1 \<in> (S 1). (snd \<sigma>1 n) mod\<^sub>o #4 = #0) \<and> (\<forall>\<sigma>2 \<in> (S 2). (snd \<sigma>2 n) mod\<^sub>o #4 = #0) \<and>
                (\<forall>\<sigma>1 \<in> (S 1). (snd \<sigma>1 i) mod\<^sub>o #4 = #3) \<and> (\<forall>\<sigma>2 \<in> (S 2). (snd \<sigma>2 i) mod\<^sub>o #4 = #0) \<and>
                (\<forall>\<sigma>1 \<in> (S 1). snd \<sigma>1 n = len (snd \<sigma>1 s)) \<and>
                (\<forall>\<sigma>2 \<in> (S 2). snd \<sigma>2 n = len (snd \<sigma>2 s)) \<and>
                (\<forall>\<sigma>1 \<in> (S 1). snd \<sigma>1 i \<ge>\<^sub>o #0) \<and>
                (\<forall>\<sigma>2 \<in> (S 2). snd \<sigma>2 i \<ge>\<^sub>o #0) \<and>
               (\<forall>\<sigma>1 \<in> (S 1). \<exists>xs::int list. (snd \<sigma>1 s) = (ListV xs)) \<and> (\<forall>\<sigma>2 \<in> (S 2). \<exists>xs::int list. (snd \<sigma>2 s) = (ListV xs)) \<and>
               (\<forall>\<sigma>1 \<in> (S 1). \<exists>n'::int. (snd \<sigma>1 n) = (#n')) \<and> (\<forall>\<sigma>2 \<in> (S 2). \<exists>n'::int. (snd \<sigma>2 n) = (#n')) \<and>
               (\<forall>\<sigma>1 \<in> (S 1). \<exists>i'::int. (snd \<sigma>1 i) = (#i')) \<and> (\<forall>\<sigma>2 \<in> (S 2). \<exists>i'::int. (snd \<sigma>2 i) = (#i')) \<and>
               (\<forall>\<sigma>1 \<in> (S 1). \<exists>x'::int. (snd \<sigma>1 x) = (#x')) \<and> 
               (\<forall>\<sigma>2 \<in> (S 2). \<exists>x0'::int. (snd \<sigma>2 x0) = (#x0')) \<and> (\<forall>\<sigma>2 \<in> (S 2). \<exists>x1'::int. (snd \<sigma>2 x1) = (#x1')) \<and>
                (\<forall>\<sigma>2 \<in> (S 2). \<exists>x2'::int. (snd \<sigma>2 x2) = (#x2')) \<and> (\<forall>\<sigma>2 \<in> (S 2). \<exists>x3'::int. (snd \<sigma>2 x3) = (#x3'))
                \<and> (holds_forall_hyper {1,2} ?bs S)
              )"

  let ?PC3 = "(\<lambda>S::int_and_list hyper_set. 
                (\<forall>\<sigma>2 \<in> (S 2). \<exists>\<sigma>1 \<in> (S 1). 
                  (snd \<sigma>1 s) = (snd \<sigma>2 s) \<and>
                  (snd \<sigma>1 x) = (snd \<sigma>2 x0) +\<^sub>o (snd \<sigma>2 x1) +\<^sub>o (snd \<sigma>2 x2) +\<^sub>o (snd \<sigma>2 x3) \<and> 
                  (snd \<sigma>1 i) = (snd \<sigma>2 i) +\<^sub>o #4
                ) \<and>
                (\<forall>\<sigma>1 \<in> (S 1). \<exists>\<sigma>2 \<in> (S 2). 
                  (snd \<sigma>1 s) = (snd \<sigma>2 s) \<and>
                  (snd \<sigma>1 x) = (snd \<sigma>2 x0) +\<^sub>o (snd \<sigma>2 x1) +\<^sub>o (snd \<sigma>2 x2) +\<^sub>o (snd \<sigma>2 x3) \<and> 
                  (snd \<sigma>1 i) = (snd \<sigma>2 i) +\<^sub>o #4
                ) \<and>
                (\<forall>\<sigma>1 \<in> (S 1). \<forall>\<sigma>1' \<in> (S 1).(snd \<sigma>1 s) = (snd \<sigma>1' s) \<and> (snd \<sigma>1 i) = (snd \<sigma>1' i)) \<and> 
                (\<forall>\<sigma>2 \<in> (S 2). \<forall>\<sigma>2' \<in> (S 2).(snd \<sigma>2 s) = (snd \<sigma>2' s) \<and> (snd \<sigma>2 i) = (snd \<sigma>2' i)) \<and> 
                (\<forall>\<sigma>1 \<in> (S 1). (snd \<sigma>1 n) mod\<^sub>o #4 = #0) \<and> (\<forall>\<sigma>2 \<in> (S 2). (snd \<sigma>2 n) mod\<^sub>o #4 = #0) \<and>
                (\<forall>\<sigma>1 \<in> (S 1). (snd \<sigma>1 i) mod\<^sub>o #4 = #0) \<and> (\<forall>\<sigma>2 \<in> (S 2). (snd \<sigma>2 i) mod\<^sub>o #4 = #0) \<and>
                (\<forall>\<sigma>1 \<in> (S 1). snd \<sigma>1 n = len (snd \<sigma>1 s)) \<and>
                (\<forall>\<sigma>2 \<in> (S 2). snd \<sigma>2 n = len (snd \<sigma>2 s)) \<and>
                (\<forall>\<sigma>1 \<in> (S 1). snd \<sigma>1 i \<ge>\<^sub>o #0) \<and>
                (\<forall>\<sigma>2 \<in> (S 2). snd \<sigma>2 i \<ge>\<^sub>o #0) \<and>
               (\<forall>\<sigma>1 \<in> (S 1). \<exists>xs::int list. (snd \<sigma>1 s) = (ListV xs)) \<and> (\<forall>\<sigma>2 \<in> (S 2). \<exists>xs::int list. (snd \<sigma>2 s) = (ListV xs)) \<and>
               (\<forall>\<sigma>1 \<in> (S 1). \<exists>n'::int. (snd \<sigma>1 n) = (#n')) \<and> (\<forall>\<sigma>2 \<in> (S 2). \<exists>n'::int. (snd \<sigma>2 n) = (#n')) \<and>
               (\<forall>\<sigma>1 \<in> (S 1). \<exists>i'::int. (snd \<sigma>1 i) = (#i')) \<and> (\<forall>\<sigma>2 \<in> (S 2). \<exists>i'::int. (snd \<sigma>2 i) = (#i')) \<and>
               (\<forall>\<sigma>1 \<in> (S 1). \<exists>x'::int. (snd \<sigma>1 x) = (#x')) \<and> 
               (\<forall>\<sigma>2 \<in> (S 2). \<exists>x0'::int. (snd \<sigma>2 x0) = (#x0')) \<and> (\<forall>\<sigma>2 \<in> (S 2). \<exists>x1'::int. (snd \<sigma>2 x1) = (#x1')) \<and>
                (\<forall>\<sigma>2 \<in> (S 2). \<exists>x2'::int. (snd \<sigma>2 x2) = (#x2')) \<and> (\<forall>\<sigma>2 \<in> (S 2). \<exists>x3'::int. (snd \<sigma>2 x3) = (#x3'))
              )"

  let ?Cs = "[1 \<mapsto> list_reduce s x i n, 2 \<mapsto> list_reduce_optimized s x i n x0 x1 x2 x3]::int_and_list hyper_program"
  let ?Cs1 = "[i \<mapsto> ((\<lambda>i. (if (i = 1) then x else x0)) i) ::= ((\<lambda>i. (\<lambda>\<sigma>. #0)) i) | i \<in> {1,2}]::int_and_list hyper_program"
  let ?Cs2.0 = "[i \<mapsto> x1 ::= (\<lambda>\<sigma>. #0) | i\<in>{2}]::int_and_list hyper_program"
  let ?Cs2.1 = "[i \<mapsto> x2 ::= (\<lambda>\<sigma>. #0) | i\<in>{2}]::int_and_list hyper_program"
  let ?Cs2.2 = "[i \<mapsto> x3 ::= (\<lambda>\<sigma>. #0) | i\<in>{2}]::int_and_list hyper_program"
  let ?Cs3 = "[j \<mapsto> i ::= (\<lambda>\<sigma>. #0)|j\<in>{1,2}]::int_and_list hyper_program"
  let ?Cs4 = "[i \<mapsto> n ::= (\<lambda>\<sigma>. len (\<sigma> s)) | i \<in> {1,2}]::int_and_list hyper_program"
  let ?CsL = "[1 \<mapsto> WHILE (\<lambda>\<sigma>. (\<sigma> i) <\<^sub>o (\<sigma> n)) DO (
    x ::= (\<lambda>\<sigma>. (\<sigma> x) +\<^sub>o (\<sigma> s) !\<^sub>o (\<sigma> i));;
    i ::= (\<lambda>\<sigma>. (\<sigma> i) +\<^sub>o #1)
  ),
  2 \<mapsto> WHILE (\<lambda>\<sigma>. ((\<sigma> i) +\<^sub>o #3) <\<^sub>o (\<sigma> n)) DO(
    x0 ::= (\<lambda>\<sigma>. (\<sigma> x0) +\<^sub>o (\<sigma> s) !\<^sub>o (\<sigma> i));;
    x1 ::= (\<lambda>\<sigma>. (\<sigma> x1) +\<^sub>o (\<sigma> s) !\<^sub>o (\<sigma> i +\<^sub>o #1));;
    x2 ::= (\<lambda>\<sigma>. (\<sigma> x2) +\<^sub>o (\<sigma> s) !\<^sub>o (\<sigma> i +\<^sub>o #2));;
    x3 ::= (\<lambda>\<sigma>. (\<sigma> x3) +\<^sub>o (\<sigma> s) !\<^sub>o (\<sigma> i +\<^sub>o #3));;
    i ::= (\<lambda>\<sigma>. (\<sigma> i) +\<^sub>o #4)
  );;
  x ::= (\<lambda>\<sigma>. (\<sigma> x0) +\<^sub>o (\<sigma> x1) +\<^sub>o (\<sigma> x2) +\<^sub>o (\<sigma> x3))]::int_and_list hyper_program"
  let ?CsL1 = "[j \<mapsto> WHILE (if (j=1) then (\<lambda>\<sigma>. (\<sigma> i) <\<^sub>o (\<sigma> n)) else (\<lambda>\<sigma>. ((\<sigma> i) +\<^sub>o #3) <\<^sub>o (\<sigma> n))) DO 
  ( if (j =1) then (
    x ::= (\<lambda>\<sigma>. (\<sigma> x) +\<^sub>o (\<sigma> s) !\<^sub>o (\<sigma> i));;
    i ::= (\<lambda>\<sigma>. (\<sigma> i) +\<^sub>o #1)
  ) else 
    (x0 ::= (\<lambda>\<sigma>. (\<sigma> x0) +\<^sub>o (\<sigma> s) !\<^sub>o (\<sigma> i));;
    x1 ::= (\<lambda>\<sigma>. (\<sigma> x1) +\<^sub>o (\<sigma> s) !\<^sub>o (\<sigma> i +\<^sub>o #1));;
    x2 ::= (\<lambda>\<sigma>. (\<sigma> x2) +\<^sub>o (\<sigma> s) !\<^sub>o (\<sigma> i +\<^sub>o #2));;
    x3 ::= (\<lambda>\<sigma>. (\<sigma> x3) +\<^sub>o (\<sigma> s) !\<^sub>o (\<sigma> i +\<^sub>o #3));;
    i ::= (\<lambda>\<sigma>. (\<sigma> i) +\<^sub>o #4))
  ) | j \<in> {1,2}]::int_and_list hyper_program"
  let ?CsL2 = "[i \<mapsto> x ::= (\<lambda>\<sigma>. (\<sigma> x0) +\<^sub>o (\<sigma> x1) +\<^sub>o (\<sigma> x2) +\<^sub>o (\<sigma> x3)) | i \<in> {2}]::int_and_list hyper_program"

  let ?P1 = "\<lambda>S. (\<forall>\<sigma>1\<in>S 1.  snd \<sigma>1 x = #0) \<and> (\<forall>\<sigma>2\<in>S 2.  snd \<sigma>2 x0 = #0)"
  let ?P2.0 = "\<lambda>S. (\<forall>\<sigma>2\<in>S 2.  snd \<sigma>2 x1 = #0)"
  let ?P2.1 = "\<lambda>S. (\<forall>\<sigma>2\<in>S 2.  snd \<sigma>2 x2 = #0)"
  let ?P2.2 = "\<lambda>S. (\<forall>\<sigma>2\<in>S 2.  snd \<sigma>2 x3 = #0)"
  let ?P3 = "\<lambda>S. (\<forall>\<sigma>1\<in>S 1.  snd \<sigma>1 i = #0) \<and> (\<forall>\<sigma>2\<in>S 2.  snd \<sigma>2 i = #0)"
  let ?P4 = "\<lambda>S. (\<forall>\<sigma>1\<in>S 1.  snd \<sigma>1 n = len (snd \<sigma>1 s)) \<and> (\<forall>\<sigma>2\<in>S 2.  snd \<sigma>2 n = len (snd \<sigma>2 s))"
  let ?PL2 = "(\<lambda>S::int_and_list hyper_set. 
                 (\<forall>\<sigma>2 \<in> (S 2). \<exists>\<sigma>1 \<in> (S 1). 
                  (snd \<sigma>1 s) = (snd \<sigma>2 s) \<and>
                  (snd \<sigma>1 x) = (snd \<sigma>2 x) \<and> 
                  (snd \<sigma>1 i) = (snd \<sigma>2 i)
                ) \<and>
                 (\<forall>\<sigma>1 \<in> (S 1). \<exists>\<sigma>2 \<in> (S 2). 
                  (snd \<sigma>1 s) = (snd \<sigma>2 s) \<and>
                  (snd \<sigma>1 x) = (snd \<sigma>2 x) \<and> 
                  (snd \<sigma>1 i) = (snd \<sigma>2 i)
                ) \<and>
                (\<forall>\<sigma>1 \<in> (S 1). \<forall>\<sigma>1' \<in> (S 1).(snd \<sigma>1 s) = (snd \<sigma>1' s) \<and> (snd \<sigma>1 i) = (snd \<sigma>1' i)) \<and> 
                (\<forall>\<sigma>2 \<in> (S 2). \<forall>\<sigma>2' \<in> (S 2).(snd \<sigma>2 s) = (snd \<sigma>2' s) \<and> (snd \<sigma>2 i) = (snd \<sigma>2' i)) \<and> 
                (\<forall>\<sigma>1 \<in> (S 1). (snd \<sigma>1 n) mod\<^sub>o #4 = #0) \<and> (\<forall>\<sigma>2 \<in> (S 2). (snd \<sigma>2 n) mod\<^sub>o #4 = #0) \<and>
                (\<forall>\<sigma>1 \<in> (S 1). (snd \<sigma>1 i) mod\<^sub>o #4 = #0) \<and> (\<forall>\<sigma>2 \<in> (S 2). (snd \<sigma>2 i) mod\<^sub>o #4 = #0) \<and>
                (\<forall>\<sigma>1 \<in> (S 1). snd \<sigma>1 n = len (snd \<sigma>1 s)) \<and>
                (\<forall>\<sigma>2 \<in> (S 2). snd \<sigma>2 n = len (snd \<sigma>2 s)) \<and>
                (\<forall>\<sigma>1 \<in> (S 1). snd \<sigma>1 i \<ge>\<^sub>o #0) \<and>
                (\<forall>\<sigma>2 \<in> (S 2). snd \<sigma>2 i \<ge>\<^sub>o #0) \<and>
               (\<forall>\<sigma>1 \<in> (S 1). \<exists>xs::int list. (snd \<sigma>1 s) = (ListV xs)) \<and> (\<forall>\<sigma>2 \<in> (S 2). \<exists>xs::int list. (snd \<sigma>2 s) = (ListV xs)) \<and>
               (\<forall>\<sigma>1 \<in> (S 1). \<exists>n'::int. (snd \<sigma>1 n) = (#n')) \<and> (\<forall>\<sigma>2 \<in> (S 2). \<exists>n'::int. (snd \<sigma>2 n) = (#n')) \<and>
               (\<forall>\<sigma>1 \<in> (S 1). \<exists>i'::int. (snd \<sigma>1 i) = (#i')) \<and> (\<forall>\<sigma>2 \<in> (S 2). \<exists>i'::int. (snd \<sigma>2 i) = (#i')) \<and>
               (\<forall>\<sigma>1 \<in> (S 1). \<exists>x'::int. (snd \<sigma>1 x) = (#x')) \<and> 
               (\<forall>\<sigma>2 \<in> (S 2). \<exists>x0'::int. (snd \<sigma>2 x0) = (#x0')) \<and> (\<forall>\<sigma>2 \<in> (S 2). \<exists>x1'::int. (snd \<sigma>2 x1) = (#x1')) \<and>
                (\<forall>\<sigma>2 \<in> (S 2). \<exists>x2'::int. (snd \<sigma>2 x2) = (#x2')) \<and> (\<forall>\<sigma>2 \<in> (S 2). \<exists>x3'::int. (snd \<sigma>2 x3) = (#x3'))
              )"
  have eq:"?Cs = ?Cs1 ;;\<^sub>H ?Cs2.0 ;;\<^sub>H ?Cs2.1 ;;\<^sub>H ?Cs2.2 ;;\<^sub>H ?Cs3 ;;\<^sub>H ?Cs4 ;;\<^sub>H ?CsL1 ;;\<^sub>H ?CsL2"
    apply(rule)
    by(auto simp add:fun_upd_def hyper_seq_def map_add_def map_comprehension_def)

  let ?LoopRep = "[j \<mapsto> repeat_with_if (if j = 1 then 4 else 1) (if j = 1 then \<lambda>\<sigma>. \<sigma> i <\<^sub>o \<sigma> n else (\<lambda>\<sigma>. \<sigma> i +\<^sub>o #3 <\<^sub>o \<sigma> n))
                                               (if j = 1 then x ::= (\<lambda>\<sigma>. \<sigma> x +\<^sub>o \<sigma> s !\<^sub>o \<sigma> i) ;; i ::= (\<lambda>\<sigma>. \<sigma> i +\<^sub>o #1)
                                                else x0 ::= (\<lambda>\<sigma>. \<sigma> x0 +\<^sub>o \<sigma> s !\<^sub>o \<sigma> i) ;;
                                                     x1 ::= (\<lambda>\<sigma>. \<sigma> x1 +\<^sub>o \<sigma> s !\<^sub>o (\<sigma> i +\<^sub>o #1)) ;;
                                                     x2 ::= (\<lambda>\<sigma>. \<sigma> x2 +\<^sub>o \<sigma> s !\<^sub>o (\<sigma> i +\<^sub>o #2)) ;;
                                                     x3 ::= (\<lambda>\<sigma>. \<sigma> x3 +\<^sub>o \<sigma> s !\<^sub>o (\<sigma> i +\<^sub>o #3)) ;; i ::= (\<lambda>\<sigma>. \<sigma> i +\<^sub>o #4)) | j \<in> {1,2}]::int_and_list hyper_program"
  let ?LoopSeq1p1 = "[j \<mapsto> if_then_else_skip (\<lambda>\<sigma>. \<sigma> i <\<^sub>o \<sigma> n) (x ::= (\<lambda>\<sigma>. \<sigma> x +\<^sub>o \<sigma> s !\<^sub>o \<sigma> i) ;; i ::= (\<lambda>\<sigma>. \<sigma> i +\<^sub>o #1)) | j \<in> {1}]::int_and_list hyper_program"
  let ?LoopSeq1p2 = "[j \<mapsto> if_then_else_skip ((\<lambda>\<sigma>. \<sigma> i +\<^sub>o #3 <\<^sub>o \<sigma> n)) (x0 ::= (\<lambda>\<sigma>. \<sigma> x0 +\<^sub>o \<sigma> s !\<^sub>o \<sigma> i) ;;
                                                     x1 ::= (\<lambda>\<sigma>. \<sigma> x1 +\<^sub>o \<sigma> s !\<^sub>o (\<sigma> i +\<^sub>o #1)) ;;
                                                     x2 ::= (\<lambda>\<sigma>. \<sigma> x2 +\<^sub>o \<sigma> s !\<^sub>o (\<sigma> i +\<^sub>o #2)) ;;
                                                     x3 ::= (\<lambda>\<sigma>. \<sigma> x3 +\<^sub>o \<sigma> s !\<^sub>o (\<sigma> i +\<^sub>o #3)) ;; i ::= (\<lambda>\<sigma>. \<sigma> i +\<^sub>o #4)) | j \<in> {2}]::int_and_list hyper_program"
  let ?LoopSeq1p2body = "[j \<mapsto> (x0 ::= (\<lambda>\<sigma>. \<sigma> x0 +\<^sub>o \<sigma> s !\<^sub>o \<sigma> i) ;;
                                 x1 ::= (\<lambda>\<sigma>. \<sigma> x1 +\<^sub>o \<sigma> s !\<^sub>o (\<sigma> i +\<^sub>o #1)) ;;
                                 x2 ::= (\<lambda>\<sigma>. \<sigma> x2 +\<^sub>o \<sigma> s !\<^sub>o (\<sigma> i +\<^sub>o #2)) ;;
                                 x3 ::= (\<lambda>\<sigma>. \<sigma> x3 +\<^sub>o \<sigma> s !\<^sub>o (\<sigma> i +\<^sub>o #3)) ;; i ::= (\<lambda>\<sigma>. \<sigma> i +\<^sub>o #4)) | j \<in> {2}]::int_and_list hyper_program"

  let ?LoopSeq2 = "[j \<mapsto> if_then_else_skip (\<lambda>\<sigma>. \<sigma> i <\<^sub>o \<sigma> n) (x ::= (\<lambda>\<sigma>. \<sigma> x +\<^sub>o \<sigma> s !\<^sub>o \<sigma> i) ;; i ::= (\<lambda>\<sigma>. \<sigma> i +\<^sub>o #1)) | j \<in> {1}]::int_and_list hyper_program" 
  let ?LoopSeq2body = "[j \<mapsto> (x ::= (\<lambda>\<sigma>. \<sigma> x +\<^sub>o \<sigma> s !\<^sub>o \<sigma> i) ;; i ::= (\<lambda>\<sigma>. \<sigma> i +\<^sub>o #1)) | j \<in> {1}]::int_and_list hyper_program" 
  let ?LoopSeqx0 = "[j \<mapsto> x0 ::= (\<lambda>\<sigma>. \<sigma> x0 +\<^sub>o \<sigma> s !\<^sub>o \<sigma> i) | j \<in> {2}]::int_and_list hyper_program"
  let ?LoopSeqx1 = "[j \<mapsto> x1 ::= (\<lambda>\<sigma>. \<sigma> x1 +\<^sub>o \<sigma> s !\<^sub>o (\<sigma> i +\<^sub>o #1)) | j \<in> {2}]::int_and_list hyper_program"
  let ?LoopSeqx2 = "[j \<mapsto> x2 ::= (\<lambda>\<sigma>. \<sigma> x2 +\<^sub>o \<sigma> s !\<^sub>o (\<sigma> i +\<^sub>o #2)) | j \<in> {2}]::int_and_list hyper_program"
  let ?LoopSeqx3 = "[j \<mapsto> x3 ::= (\<lambda>\<sigma>. \<sigma> x3 +\<^sub>o \<sigma> s !\<^sub>o (\<sigma> i +\<^sub>o #3)) | j \<in> {2}]::int_and_list hyper_program"
  let ?LoopSeqi = "[j \<mapsto> i ::= (\<lambda>\<sigma>. \<sigma> i +\<^sub>o #4) | j \<in> {2}]::int_and_list hyper_program"
  let ?Skips = "[j\<mapsto> Skip | j \<in> {1,2}]::int_and_list hyper_program"
  let ?LoopSeq2bodyi = "[j \<mapsto> i ::= (\<lambda>\<sigma>. \<sigma> i +\<^sub>o #1) | j \<in> {1}]::int_and_list hyper_program"
  let ?LoopSeqComb0 = "[j\<mapsto>((if (j=1) then x else x0) ::= (if (j=1) then (\<lambda>\<sigma>. \<sigma> x +\<^sub>o \<sigma> s !\<^sub>o \<sigma> i) else (\<lambda>\<sigma>. \<sigma> x0 +\<^sub>o \<sigma> s !\<^sub>o \<sigma> i)))|j\<in>{1,2}]"
  let ?LoopSeqComb1= "[j\<mapsto>((if (j=1) then x else x1) ::= (if (j=1) then (\<lambda>\<sigma>. \<sigma> x +\<^sub>o \<sigma> s !\<^sub>o \<sigma> i) else (\<lambda>\<sigma>. \<sigma> x1 +\<^sub>o \<sigma> s !\<^sub>o (\<sigma> i +\<^sub>o #1))))|j\<in>{1,2}]"
  let ?LoopSeqComb2= "[j\<mapsto>((if (j=1) then x else x2) ::= (if (j=1) then (\<lambda>\<sigma>. \<sigma> x +\<^sub>o \<sigma> s !\<^sub>o \<sigma> i) else (\<lambda>\<sigma>. \<sigma> x2 +\<^sub>o \<sigma> s !\<^sub>o (\<sigma> i +\<^sub>o #2))))|j\<in>{1,2}]"
  let ?LoopSeqComb3= "[j\<mapsto>((if (j=1) then x else x3) ::= (if (j=1) then (\<lambda>\<sigma>. \<sigma> x +\<^sub>o \<sigma> s !\<^sub>o \<sigma> i) else (\<lambda>\<sigma>. \<sigma> x3 +\<^sub>o \<sigma> s !\<^sub>o (\<sigma> i +\<^sub>o #3))))|j\<in>{1,2}]"

  have eq2: "?LoopRep = (?LoopSeq1p1 ++ ?LoopSeq1p2) ;;\<^sub>H ?LoopSeq2 ;;\<^sub>H ?LoopSeq2 ;;\<^sub>H ?LoopSeq2 ;;\<^sub>H ?Skips"
    apply(rule)
    apply(auto simp add:fun_upd_def hyper_seq_def map_add_def map_comprehension_def)
    by (simp add: numeral_eq_Suc)

  have eq3: "(?LoopSeq1p1 ++ ?LoopSeq1p2) ;;\<^sub>H ?LoopSeq2 ;;\<^sub>H ?LoopSeq2 ;;\<^sub>H ?LoopSeq2 = (?LoopSeq1p1 ;;\<^sub>H ?LoopSeq2 ;;\<^sub>H ?LoopSeq2 ;;\<^sub>H ?LoopSeq2) ++ ?LoopSeq1p2"
    apply(rule)
    by(auto simp add:fun_upd_def hyper_seq_def map_add_def map_comprehension_def)

  have eq4: "(?LoopSeq1p1 ;;\<^sub>H ?LoopSeq2 ;;\<^sub>H ?LoopSeq2 ;;\<^sub>H ?LoopSeq2) ++ ?LoopSeq1p2body 
        = (?LoopSeqx0++?LoopSeq2) ;;\<^sub>H (?LoopSeqx1++?LoopSeq2) ;;\<^sub>H (?LoopSeqx2++?LoopSeq2) ;;\<^sub>H (?LoopSeqx3++?LoopSeq2) ;;\<^sub>H ?LoopSeqi"
    apply(rule)
    by(auto simp add:fun_upd_def hyper_seq_def map_add_def map_comprehension_def)

  have eqc0: "?LoopSeqx0 ++ ?LoopSeq2body  = (?LoopSeqComb0 ;;\<^sub>H ?LoopSeq2bodyi)"
    apply(rule)
    by(auto simp add:fun_upd_def hyper_seq_def map_add_def map_comprehension_def)
  have eqc1: "?LoopSeqx1 ++ ?LoopSeq2body  = (?LoopSeqComb1 ;;\<^sub>H ?LoopSeq2bodyi)"
    apply(rule)
    by(auto simp add:fun_upd_def hyper_seq_def map_add_def map_comprehension_def)
  have eqc2: "?LoopSeqx2 ++ ?LoopSeq2body  = (?LoopSeqComb2 ;;\<^sub>H ?LoopSeq2bodyi)"
    apply(rule)
    by(auto simp add:fun_upd_def hyper_seq_def map_add_def map_comprehension_def)
  have eqc3: "?LoopSeqx3 ++ ?LoopSeq2body  = (?LoopSeqComb3 ;;\<^sub>H ?LoopSeq2bodyi)"
    apply(rule)
    by(auto simp add:fun_upd_def hyper_seq_def map_add_def map_comprehension_def)

  show ?thesis
    apply(simp only:eq)
    apply(rule seq_extension[where ?R = "conj ?P ?P1"])
     apply(rule cons_prec)
    prefer 2
      apply(rule assign_lockstep)
        using assms
        unfolding entails_def 
         apply(simp only:conj_def)
         apply(intro allI impI conjI)
                apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(2) assms by(fastforce) qed
               apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(3) assms by(fastforce) qed
              apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(4) assms by(fastforce) qed
             apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(5) assms by(fastforce) qed
            apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(6) assms by(fastforce) qed
           apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(7) assms by(fastforce) qed
            apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(8) assms by(fastforce) qed
           apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(9) assms by(fastforce) qed
          apply(erule conjE)+
        subgoal premises prems proof - show ?thesis by(fastforce) qed
         apply(erule conjE)+
        subgoal premises prems proof - show ?thesis by(fastforce) qed
        apply(rule seq_extension[where ?R = "conj (conj ?P ?P1) ?P2.0"])
         apply(rule cons_prec)
          prefer 2
          apply(rule assign_lockstep)
          using assms
          unfolding entails_def 
           apply(simp only:conj_def)
          apply(simp only: conj_assoc)
           apply(intro allI impI conjI)
                   apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(2) assms by (smt (verit) distinct_length_2_or_more fun_upd_apply mem_Collect_eq singleton_iff snd_eqD) qed
                  apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(3) assms by(fastforce) qed
                 apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(4) assms by(fastforce) qed
             apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(5) assms by(fastforce) qed
            apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(6) assms by(fastforce) qed
           apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(7) assms by(fastforce) qed
           apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(8) assms by(fastforce) qed
          apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(9) assms by(fastforce) qed
           apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(10) assms by(fastforce) qed
           apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(11) assms by(fastforce) qed
          apply(erule conjE)+
        subgoal premises prems proof - show ?thesis by(fastforce) qed
        apply(rule seq_extension[where ?R = "conj (conj (conj ?P ?P1) ?P2.0) ?P2.1"])
         apply(rule cons_prec)
          prefer 2
          apply(rule assign_lockstep)
          using assms
          unfolding entails_def 
           apply(simp only:conj_def)
          apply(simp only: conj_assoc)
           apply(intro allI impI conjI)
                    apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(2) assms by force qed
                   apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(3) assms by(fastforce) qed
                 apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(4) assms by(fastforce) qed
             apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(5) assms by(fastforce) qed
            apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(6) assms by(fastforce) qed
           apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(7) assms by(fastforce) qed
           apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(8) assms by(fastforce) qed
          apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(9) assms by(fastforce) qed
          apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(10) assms by(fastforce) qed
           apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(11) assms by(fastforce) qed
           apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(12) assms by(fastforce) qed
          apply(erule conjE)+
        subgoal premises prems proof - show ?thesis by(fastforce) qed
        apply(rule seq_extension[where ?R = "conj (conj (conj (conj ?P ?P1) ?P2.0) ?P2.1) ?P2.2"])
         apply(rule cons_prec)
          prefer 2
          apply(rule assign_lockstep)
          using assms
          unfolding entails_def 
           apply(simp only:conj_def)
          apply(simp only: conj_assoc)
           apply(intro allI impI conjI)
                    apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(2) assms by(force) qed
                   apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(3) assms by(fastforce) qed
                 apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(4) assms by(fastforce) qed
             apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(5) assms by(fastforce) qed
            apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(6) assms by(fastforce) qed
           apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(7) assms by(fastforce) qed
           apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(8) assms by(fastforce) qed
          apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(9) assms by(fastforce) qed
          apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(10) assms by(fastforce) qed
          apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(11) assms by(fastforce) qed
        apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(12) assms by(fastforce) qed
           apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(13) assms by(fastforce) qed
          apply(erule conjE)+
        subgoal premises prems proof - show ?thesis by(fastforce) qed
        apply(rule seq_extension[where ?R = "conj (conj (conj (conj (conj ?P ?P1) ?P2.0) ?P2.1) ?P2.2) ?P3"])
         apply(rule cons_prec)
          prefer 2
          apply(rule assign_lockstep)
          using assms
          unfolding entails_def 
           apply(simp only:conj_def)
          apply(simp only: conj_assoc)
           apply(intro allI impI conjI)
                    apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(2) by(fastforce) qed
                   apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(3) assms by(fastforce) qed
                 apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(4) assms by(fastforce) qed
             apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(5) assms by(fastforce) qed
            apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(6) assms by(fastforce) qed
           apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(7) assms by(fastforce) qed
           apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(8) assms by(fastforce) qed
          apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(9) assms by(fastforce) qed
          apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(10) assms by(fastforce) qed
          apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(11) assms by(fastforce) qed
           apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(12) assms by(fastforce) qed
            apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(13) assms by(fastforce) qed
           apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(14) assms by(fastforce) qed
          apply(erule conjE)+
        subgoal premises prems proof - show ?thesis by(fastforce) qed
         apply(erule conjE)+
        subgoal premises prems proof - show ?thesis by(fastforce) qed
        apply(rule seq_extension[where ?R = "conj (conj (conj (conj (conj (conj ?P ?P1) ?P2.0) ?P2.1) ?P2.2) ?P3) ?P4"])
         apply(rule cons_prec)
          prefer 2
          apply(rule assign_lockstep)
          using assms
          unfolding entails_def 
           apply(simp only:conj_def)
          apply(simp only: conj_assoc)
           apply(intro allI impI conjI)
                    apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(2) by(fastforce) qed
                   apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(3) assms by(fastforce) qed
                 apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(4) assms by(fastforce) qed
             apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(5) assms by(fastforce) qed
            apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(6) assms by(fastforce) qed
           apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(7) assms by(fastforce) qed
           apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(8) assms by(fastforce) qed
          apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(9) assms by(fastforce) qed
          apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(10) assms by(fastforce) qed
          apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(11) assms by(fastforce) qed
           apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(12) assms by(fastforce) qed
            apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(13) assms by(fastforce) qed
           apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(14) assms by(fastforce) qed
            apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(15) assms by(fastforce) qed
           apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using prems(16) assms by(fastforce) qed
          apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using assms by(fastforce) qed
          apply(erule conjE)+
        subgoal premises prems proof - show ?thesis using assms by(fastforce) qed
        apply(rule cons_prec[where ?P'="?Iv"])
          using assms
          unfolding entails_def 
           apply(simp only:conj_def)
          apply(simp only: conj_assoc)
           apply(intro allI impI conjI)
                apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(2) prems(10-16) by(fastforce) qed
                              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(3) prems(10-16) by(fastforce) qed
                apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(4) prems(15) by metis qed
                apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(5) prems(16) by metis qed
                       apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(17) prems(6) by metis qed
                      apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(18) prems(7) by metis qed
                     apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(15) by auto qed
                      apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(16) by auto qed
             apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(17) prems(15) prems(8) by(auto) qed
            apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(18) prems(16) prems(9) by(auto) qed
                         apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(15) by(fastforce) qed
           apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(16) by(fastforce) qed
                        apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(8) by(fastforce) qed
           apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(9) by(fastforce) qed
              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(17) prems(8) by(fastforce) qed
             apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(18) prems(9) by(fastforce) qed
            apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(15) by(fastforce) qed
           apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(16) by(fastforce) qed
                apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(10) by(fastforce) qed
               apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(11) by(fastforce) qed
             apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(12) by(fastforce) qed
            apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(13) by(fastforce) qed
           apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(14) by(fastforce) qed
          apply(rule seq_extension[where ?R="conj ?Iv (holds_forall_hyper {1,2} (lnot_hyper ?bs))"])
           prefer 2
           apply(rule cons_post[where Q'="?PL2"])
          using assms
          unfolding entails_def 
            apply(intro allI impI conjI)
            apply(erule conjE)+
          apply metis
            apply(rule cons_prec)
             prefer 2
          apply(rule assign_lockstep)
          using assms
          unfolding entails_def 
           apply(simp only:conj_def)
          apply(simp only: conj_assoc)
           apply(intro allI impI conjI)
                          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(2) assms by(force) qed
                         apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(3) by(fastforce) qed
                        apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(4) assms by(fastforce) qed
                       apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(5) assms by(fastforce) qed
                      apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(6) assms by(fastforce) qed
                     apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(7) assms by(fastforce) qed
                    apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(8) assms by(fastforce) qed
                   apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(9) assms by(fastforce) qed
                  apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(10) assms by(fastforce) qed
                 apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(11) assms by(fastforce) qed
                apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(12) assms by(fastforce) qed
               apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(13) assms by(fastforce) qed
              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(14) assms by(fastforce) qed
             apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(15) assms by(fastforce) qed
            apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(16) assms by(fastforce) qed
           apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(17) assms by(fastforce) qed
                 apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(18) assms by(fastforce) qed
                apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(19) assms by(fastforce) qed
               apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(20) assms by(fastforce) qed
              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(21) assms by(fastforce) qed
             apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(22) assms by(fastforce) qed
            apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(23) assms by(fastforce) qed
            apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(24) assms by(fastforce) qed
          apply(rule cons_prec)
           prefer 2
           apply(rule cons_post)
           prefer 2
            apply(rule while_fixed_lck[where Iv="?Iv" and rf="?rf"])
             prefer 2
             apply(simp)
            prefer 2
          unfolding entails_def
           apply(simp only:conj_def disj_def)
            apply(simp only: conj_assoc)
           apply(intro allI impI)
                          apply(erule conjE)+
          subgoal premises prems proof - from prems(1) show ?thesis 
              apply(rule) 
              subgoal premises prems2 proof - from prems2 prems(2) show ?thesis by fastforce qed
              using prems(2) unfolding hyper_emp_def by fastforce
          qed
          prefer 2
           apply(simp only:conj_def)
            apply(simp only: conj_assoc)
           apply(intro allI impI conjI)
                          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(1) by(fastforce) qed
                         apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(2) by(fastforce) qed
                        apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(3) assms by(fastforce) qed
                       apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(4) assms by(fastforce) qed
                      apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(5) assms by(fastforce) qed
                     apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(6) assms by(fastforce) qed
                    apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(7) assms by(fastforce) qed
                   apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(8) assms by(fastforce) qed
                  apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(9) assms by(fastforce) qed
                 apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(10) assms by(fastforce) qed
                apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(11) assms by(fastforce) qed
               apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(12) assms by(fastforce) qed
              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(13) assms by(fastforce) qed
             apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(14) assms by(fastforce) qed
            apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(15) assms by(fastforce) qed
           apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(16) assms by(fastforce) qed
                  apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(17) assms by(fastforce) qed
                 apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(18) assms by(fastforce) qed
                apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(19) assms by(fastforce) qed
               apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(20) assms by(fastforce) qed
              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(21) assms by(fastforce) qed
             apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(22) assms by(fastforce) qed
            apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(23) assms by(fastforce) qed
            apply(erule conjE)+
          subgoal premises prems for S proof - 
            from prems(1,2,3,4) have H:"\<forall>\<sigma>2\<in>S 2. \<forall>\<sigma>1\<in>S 1. snd \<sigma>1 s = snd \<sigma>2 s \<and> snd \<sigma>1 i = snd \<sigma>2 i" by fastforce
            show ?thesis unfolding low_exp_hyper_def
              apply(intro ballI allI impI)
              apply(auto)
              using prems(2,3) prems(9) apply (metis One_nat_def snd_conv)
              using prems(2,3) prems(9) apply (metis One_nat_def snd_conv)
              using H prems(9,10) prems(15,16,17,18) prems(7) prems(5) apply fastforce
              using H prems(9,10) prems(15,16,17,18) prems(6) prems(4) apply fastforce
              using H prems(9,10) prems(15,16,17,18) prems(6) prems(4) apply fastforce
              using H prems(9,10) prems(15,16,17,18) prems(7) prems(5) apply fastforce
              using prems(4) prems(10) apply (metis snd_conv)
              using prems(4) prems(10) apply (metis snd_conv)
              done
          qed
          apply(simp only:eq2)
          apply(simp only: seq_associativity)
          apply(rule seq_extension[where ?R="?Iv"])
           apply(simp only: seq_associativity[symmetric])
           apply(simp only:eq3)
           apply(rule cons_prec)
            prefer 2
          apply(simp only:if_then_else_skip_def)
            apply(rule if_true_lck[where P="conj ?Iv (holds_forall_hyper {1,2} ?bs)"])
          prefer 3
          using assms
          unfolding entails_def 
           apply(simp only:conj_def)
          apply(simp only: conj_assoc)
           apply(intro allI impI conjI)
                          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(2) by(fastforce) qed
                         apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(3) by(fastforce) qed
                        apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(4) assms by(fastforce) qed
                       apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(5) assms by(fastforce) qed
                      apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(6) assms by(fastforce) qed
                     apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(7) assms by(fastforce) qed
                    apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(8) assms by(fastforce) qed
                   apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(9) assms by(fastforce) qed
                  apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(10) assms by(fastforce) qed
                 apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(11) assms by(fastforce) qed
                apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(12) assms by(fastforce) qed
               apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(13) assms by(fastforce) qed
              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(14) assms by(fastforce) qed
             apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(15) assms by(fastforce) qed
            apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(16) assms by(fastforce) qed
           apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(17) assms by(fastforce) qed
             apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(18)  by(fastforce) qed
                    apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(19)  by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(20)  by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(21)  by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(22)  by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(23)  by(fastforce) qed
               apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(24)  by(fastforce) qed
             apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(25)  by(fastforce) qed
             apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(25) unfolding holds_forall_hyper_def by(fastforce) qed
            prefer 2
            apply(simp add:map_comprehension_def hyper_seq_def dom_def)
          apply(simp only:if_then_else_skip_def[symmetric])
           apply(simp only:eq4)
           apply(rule seq_extension[where ?R="?PC0"])
           apply(rule cons_prec)
            prefer 2
          apply(simp only:if_then_else_skip_def)
             apply(rule if_true_lck[where P="conj ?Iv (holds_forall_hyper {1,2} ?bs)"])
          prefer 2
              apply(simp add:map_comprehension_def hyper_seq_def dom_def)
             prefer 2
        using assms
          unfolding entails_def 
           apply(simp only:conj_def)
          apply(simp only: conj_assoc)
           apply(intro allI impI conjI)
                          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(2) by(fastforce) qed
                         apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(3) by(fastforce) qed
                        apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(4) assms by(fastforce) qed
                       apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(5) assms by(fastforce) qed
                      apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(6) assms by(fastforce) qed
                     apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(7) assms by(fastforce) qed
                    apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(8) assms by(fastforce) qed
                   apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(9) assms by(fastforce) qed
                  apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(10) assms by(fastforce) qed
                 apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(11) assms by(fastforce) qed
                apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(12) assms by(fastforce) qed
               apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(13) assms by(fastforce) qed
              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(14) assms by(fastforce) qed
             apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(15) assms by(fastforce) qed
            apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(16) assms by(fastforce) qed
           apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(17) assms by(fastforce) qed
                     apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(18) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(19) assms by(fastforce) qed
                   apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(20) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(21) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(22) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(23) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(24) assms by(fastforce) qed
             apply(erule conjE)+
          subgoal premises prems for S proof - show ?thesis using prems(25)  by fastforce qed
             apply(erule conjE)+
          subgoal premises prems for S proof - show ?thesis using prems(25) unfolding holds_forall_hyper_def by fastforce qed
            apply(simp only:eqc0)
            apply(rule seq_extension[where ?R="conj ?Iv (holds_forall_hyper {1,2} ?bs)"])
             apply(rule cons_prec)
          prefer 2
          apply(rule assign_lockstep)
                   using assms
          unfolding entails_def 
           apply(simp only:conj_def)
          apply(simp only: conj_assoc)
           apply(intro allI impI conjI)
                              apply(erule conjE)+
          subgoal premises prems for S proof - show ?thesis using prems(2) prems(25) prems(9,10) prems(11,12) prems(14-24) assms unfolding holds_forall_hyper_def by fastforce qed
                              apply(erule conjE)+
          subgoal premises prems for S proof - show ?thesis using prems(3) prems(25) prems(9,10) prems(11,12) prems(14-24) assms unfolding holds_forall_hyper_def by fastforce qed
                        apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(4) assms by(fastforce) qed
                       apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(5) assms by(fastforce) qed
                      apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(6) assms by(fastforce) qed
                     apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(7) assms by(fastforce) qed
                    apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(8) assms by(fastforce) qed
                   apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(9) assms by(fastforce) qed
                  apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(10) assms by(fastforce) qed
                           apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(11) assms by(fastforce) qed
                          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(12) assms by(fastforce) qed
            (*proof (intro ballI)
              fix \<sigma>2 \<sigma>1
              assume asm1:"\<sigma>2 \<in> (if 2 \<in> {1::int, 2} then {(l, \<sigma>(if (2::int) = 1 then x else x0 := (if (2::int) = 1 then \<lambda>\<sigma>. \<sigma> x +\<^sub>o \<sigma> s !\<^sub>o \<sigma> i else (\<lambda>\<sigma>. \<sigma> x0 +\<^sub>o \<sigma> s !\<^sub>o \<sigma> i)) \<sigma>)) |l \<sigma>. (l, \<sigma>) \<in> S 2}
               else S 2)"
              assume asm2:"\<sigma>1 \<in> (if 1 \<in> {1::int, 2} then {(l, \<sigma>(if (1::int) = 1 then x else x0 := (if (1::int) = 1 then \<lambda>\<sigma>. \<sigma> x +\<^sub>o \<sigma> s !\<^sub>o \<sigma> i else (\<lambda>\<sigma>. \<sigma> x0 +\<^sub>o \<sigma> s !\<^sub>o \<sigma> i)) \<sigma>)) |l \<sigma>. (l, \<sigma>) \<in> S 1}
               else S 1)"
              from prems(12,13) prems(16,17) asm1 asm2 assms obtain xs1 xs2 i1' i2' where fxs1:"snd \<sigma>1 s = ListV xs1" 
                                                                and fxs2:"snd \<sigma>2 s = ListV xs2"
                                                                and fi:"snd \<sigma>1 i = #i1'"
                                                                and fi2:"snd \<sigma>2 i = #i2'" by fastforce
              from  asm2 assms prems(9) have fn1:"snd \<sigma>1 n = len (snd \<sigma>1 s)"  by fastforce 
              from asm1  assms prems(10) have fn2:"snd \<sigma>2 n = len (snd \<sigma>2 s)"  by fastforce 
              from asm1 asm2 assms prems(11) have fs:"snd \<sigma>1 s = snd \<sigma>2 s" by fastforce
              from asm1 asm2 assms prems(11) have fis:"snd \<sigma>1 i = snd \<sigma>2 i" by fastforce
              from asm1 obtain \<sigma>2' where "\<sigma>2'\<in>(S 2)" and "\<sigma>2 = (fst \<sigma>2', (snd \<sigma>2')(x0 := (snd \<sigma>2') x0 +\<^sub>o (snd \<sigma>2') s !\<^sub>o (snd \<sigma>2') i))" by auto
              from this have "snd \<sigma>2 x0 = snd \<sigma>2' x0 +\<^sub>o snd \<sigma>2' s !\<^sub>o snd \<sigma>2' i" by auto
              from asm2 obtain \<sigma>1' where "\<sigma>1'\<in>(S 1)" and "\<sigma>1 = (fst \<sigma>1', (snd \<sigma>1')(x := (snd \<sigma>1') x +\<^sub>o (snd \<sigma>1') s !\<^sub>o (snd \<sigma>1') i))" by auto
              from this have "snd \<sigma>1 x = snd \<sigma>1' x +\<^sub>o snd \<sigma>2' s !\<^sub>o snd \<sigma>2' i" by auto
              from fxs1 fxs2 fi fi2 fn1 fn2 fs fis prems(11) asm1 asm2 have "snd \<sigma>1 x = snd \<sigma>2 x0 +\<^sub>o snd \<sigma>2 x1 +\<^sub>o snd \<sigma>2 x2 +\<^sub>o snd \<sigma>2 x3"
            qed*)
                apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(13) assms by(fastforce) qed
               apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(14) assms by(fastforce) qed
              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(15) assms by(fastforce) qed
             apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(16) assms by(fastforce) qed
            apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(17) assms by(fastforce) qed
           apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(18) assms by(fastforce) qed
                   apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(19) assms by(fastforce) qed
                  apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(20) prems(18) prems(14) prems(10) prems(12) assms by(fastforce) qed
                 apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(21) prems(19) prems(15) prems(11) prems(13) prems(2,3) assms by(fastforce) qed
                apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(22) assms by(fastforce) qed
               apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(23) assms by(fastforce) qed
              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(24) assms by(fastforce) qed
             apply(erule conjE)+
          subgoal premises prems for S proof - show ?thesis using prems(25) assms unfolding holds_forall_hyper_def by fastforce qed
            apply(rule cons_prec)
             prefer 2
             apply(rule assign_lockstep)
          using assms
          unfolding entails_def 
           apply(simp only:conj_def)
          apply(simp only: conj_assoc)
           apply(intro allI impI conjI)
                          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(2) assms by(fastforce) qed
                              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(3) assms by(force) qed
                              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(4) assms by(fastforce) qed
                              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(5) assms by(fastforce) qed
                              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(6) assms by(fastforce) qed
                              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(7) assms by(fastforce) qed
                              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(8) assms prems(18) by(fastforce) qed
                             apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(9) assms by(fastforce) qed
                            apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(10) assms by(fastforce) qed
                           apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(11) assms by(fastforce) qed
                          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(12) prems(18) assms by(fastforce) qed
                         apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(13) assms by(fastforce) qed
                       apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(14) assms by(fastforce) qed
                      apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(15) assms by(fastforce) qed
                     apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(16) assms by(fastforce) qed
                    apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(17) assms by(fastforce) qed
                   apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(18) assms by(fastforce) qed
                  apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(19) assms by(fastforce) qed
                 apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(20) assms by(fastforce) qed
                apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(21) assms by(fastforce) qed
               apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(22) assms by(fastforce) qed
              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(23) assms by(fastforce) qed
             apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(24) assms by(fastforce) qed
            apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(25) prems(8) prems(6) prems(18) prems(16) assms unfolding holds_forall_hyper_def by(fastforce) qed
           apply(rule seq_extension[where ?R="?PC1"])
           apply(rule cons_prec)
            prefer 2
          apply(simp only:if_then_else_skip_def)
             apply(rule if_true_lck[where P="?PC0"])
          prefer 2
              apply(simp add:map_comprehension_def hyper_seq_def dom_def)
             prefer 2
        using assms
          unfolding entails_def 
           apply(simp only:conj_def)
          apply(simp only: conj_assoc)
           apply(intro allI impI conjI)
                          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(2) by(fastforce) qed
                              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(3) by(fastforce) qed
                         apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(4) by(fastforce) qed
                        apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(5) assms by(fastforce) qed
                       apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(6) assms by(fastforce) qed
                      apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(7) assms by(fastforce) qed
                     apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(8) assms by(fastforce) qed
                    apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(9) assms by(fastforce) qed
                   apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(10) assms by(fastforce) qed
                  apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(11) assms by(fastforce) qed
                 apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(12) assms by(fastforce) qed
                apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(13) assms by(fastforce) qed
              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(14) assms by(fastforce) qed
             apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(15) assms by(fastforce) qed
            apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(16) assms by(fastforce) qed
           apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(17) assms by(fastforce) qed
                     apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(18) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(19) assms by(fastforce) qed
                   apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(20) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(21) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(22) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(23) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(24) assms by(fastforce) qed
             apply(erule conjE)+
          subgoal premises prems for S proof - show ?thesis using prems(25)  by fastforce qed
             apply(erule conjE)+
          subgoal premises prems for S proof - show ?thesis using prems(25) unfolding holds_forall_hyper_def by fastforce qed
            apply(simp only:eqc1)
            apply(rule seq_extension[where ?R="?PC0"])
             apply(rule cons_prec)
          prefer 2
          apply(rule assign_lockstep)
                   using assms
          unfolding entails_def 
           apply(simp only:conj_def)
          apply(simp only: conj_assoc)
           apply(intro allI impI conjI)
                              apply(erule conjE)+
          subgoal premises prems for S proof - show ?thesis using prems(2) prems(25) prems(10,11) prems(12,13) prems(14-24) assms unfolding holds_forall_hyper_def by fastforce qed
                         apply(erule conjE)+
          subgoal premises prems for S proof - show ?thesis using prems(3) prems(25) prems(10,11) prems(12,13) prems(14-24) assms unfolding holds_forall_hyper_def by fastforce qed
                        apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(4) assms by(fastforce) qed
                       apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(5) assms by(fastforce) qed
                      apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(6) assms by(fastforce) qed
                     apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(7) assms by(fastforce) qed
                    apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(8) assms by(fastforce) qed
                   apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(9) assms by(fastforce) qed
                  apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(10) assms by(fastforce) qed
                           apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(11) assms by(fastforce) qed
                          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(12) assms by(fastforce) qed
                         apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(13) assms by(fastforce) qed
                 apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(14) assms by(fastforce) qed
               apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(15) assms by(fastforce) qed
              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(16) assms by(fastforce) qed
             apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(17) assms by(fastforce) qed
            apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(18) assms by(fastforce) qed
           apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(19) assms by(fastforce) qed
                  apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(20) prems(18) prems(14) prems(10) prems(12) assms by(fastforce) qed
                 apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(21)  assms by(fastforce) qed
                apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(22) prems(19) prems(15) prems(11) prems(13)  assms by(fastforce) qed
               apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(23) assms by(fastforce) qed
              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(24) assms by(fastforce) qed
             apply(erule conjE)+
          subgoal premises prems for S proof - show ?thesis using prems(25) assms unfolding holds_forall_hyper_def by fastforce qed
            apply(rule cons_prec)
             prefer 2
             apply(rule assign_lockstep)
          using assms
          unfolding entails_def 
           apply(intro allI impI conjI)
                              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(2) prems(18,19) assms by(fastforce) qed
                              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(3) prems(18,19) assms apply(auto)
            by (smt (verit) plus_ol.simps(1) snd_conv) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(4) assms by(fastforce) qed
                              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(5) assms by(fastforce) qed
                              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(6) assms by(fastforce) qed
                              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(7) assms by(fastforce) qed
                              apply(erule conjE)+
          subgoal premises prems for S proof - show ?thesis using prems(8) assms prems(18) 
            proof (intro ballI)
              fix  \<sigma>1
              assume asm1:"\<sigma>1 \<in> (if 1 \<in> {1::nat} then {(l, \<sigma>(i := \<sigma> i +\<^sub>o #1)) |l \<sigma>. (l, \<sigma>) \<in> S 1} else S 1)"
              from asm1  obtain \<sigma>1' where fsg:"\<sigma>1' \<in> (S 1)" and fsg2:"\<sigma>1=(fst \<sigma>1', (snd \<sigma>1')(i := (snd \<sigma>1') i +\<^sub>o #1))" by fastforce
              from asm1  prems(18) assms obtain i' where fi:"snd \<sigma>1 i = #i'" by fastforce
              from fsg prems(18) obtain i2' where fi2:"snd \<sigma>1' i = #i2'" by fastforce

              have fis:"snd \<sigma>1 i = snd \<sigma>1' i +\<^sub>o #1" using fsg2 by fastforce
              from prems(8) fsg have fmodi:"snd \<sigma>1' i mod\<^sub>o #4 = #1" by fastforce

              show "snd \<sigma>1 i mod\<^sub>o #4 = #2" using  fi  fi2 fis fmodi 
                apply(auto)
                by presburger
            qed
          qed
                             apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(9) assms by(fastforce) qed
                            apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(10) assms by(fastforce) qed
                           apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(11) assms by(fastforce) qed
                          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(12) prems(18) assms by(fastforce) qed
                         apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(13) assms by(fastforce) qed
                       apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(14) assms by(fastforce) qed
                      apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(15) assms by(fastforce) qed
                     apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(16) assms by(fastforce) qed
                    apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(17) assms by(fastforce) qed
                   apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(18) assms by(fastforce) qed
                  apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(19) assms by(fastforce) qed
                 apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(20) assms by(fastforce) qed
                apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(21) assms by(fastforce) qed
               apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(22) assms by(fastforce) qed
              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(23) assms by(fastforce) qed
             apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(24) assms by(fastforce) qed
            apply(erule conjE)+
          subgoal premises prems for S proof - show ?thesis using prems(25) prems(8) prems(6) prems(18) prems(16) assms unfolding holds_forall_hyper_def 
            proof (intro ballI)
              fix j::nat
              fix  \<sigma>
              assume asm1:"\<sigma> \<in> (if j \<in> {1} then {(l, \<sigma>(i := \<sigma> i +\<^sub>o #1)) |l \<sigma>. (l, \<sigma>) \<in> S j} else S j)"
              assume "j \<in> {1,2::nat}"
              hence "j = 2 \<or> j = 1" by auto
              thus "(if j = 1 then \<lambda>\<sigma>. \<sigma> i <\<^sub>o \<sigma> n else (\<lambda>\<sigma>. \<sigma> i +\<^sub>o #3 <\<^sub>o \<sigma> n)) (snd \<sigma>)"
              proof
                assume "j=2"
                thus ?thesis using prems(25) asm1 unfolding holds_forall_hyper_def by fastforce
              next 
                assume asm2:"j=1"
                from asm1 asm2 obtain \<sigma>' where fsg:"\<sigma>' \<in> (S 1)" and fsg2:"\<sigma>=(fst \<sigma>', (snd \<sigma>')(i := (snd \<sigma>') i +\<^sub>o #1))" by fastforce
                from asm1 asm2 prems(16) assms obtain n' where fn:"snd \<sigma> n = #n'" by fastforce
                from asm1 asm2 prems(18) assms obtain i' where fi:"snd \<sigma> i = #i'" by fastforce
                from fsg prems(16) obtain n2' where fn2:"snd \<sigma>' n = #n2'" by fastforce
                from fsg prems(18) obtain i2' where fi2:"snd \<sigma>' i = #i2'" by fastforce

                have fis:"snd \<sigma> i = snd \<sigma>' i +\<^sub>o #1" using fsg2 by fastforce
                from prems(25) fsg have fle:"snd \<sigma>' i <\<^sub>o snd \<sigma>' n" unfolding holds_forall_hyper_def by fastforce
                from prems(6) fsg have fmodn:"snd \<sigma>' n mod\<^sub>o #4 = #0" by fastforce
                from prems(8) fsg have fmodi:"snd \<sigma>' i mod\<^sub>o #4 = #1" by fastforce
                have fns:"snd \<sigma> n = snd \<sigma>' n" using fsg2 assms by fastforce

                have "snd \<sigma> i <\<^sub>o snd \<sigma> n" using fn fi fn2 fi2 fis fle fmodn fmodi fns
                  apply(auto)
                  by presburger
                thus ?thesis using asm2 by auto
              qed
            qed
          qed
           apply(rule seq_extension[where ?R="?PC2"])
           apply(rule cons_prec)
            prefer 2
          apply(simp only:if_then_else_skip_def)
             apply(rule if_true_lck[where P="?PC1"])
          prefer 2
              apply(simp add:map_comprehension_def hyper_seq_def dom_def)
             prefer 2
        using assms
          unfolding entails_def 
           apply(simp only:conj_def)
          apply(simp only: conj_assoc)
           apply(intro allI impI conjI)
                          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(2) by(fastforce) qed
                         apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(3) by(fastforce) qed
                        apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(4) assms by(fastforce) qed
                       apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(5) assms by(fastforce) qed
                      apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(6) assms by(fastforce) qed
                     apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(7) assms by(fastforce) qed
                    apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(8) assms by(fastforce) qed
                   apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(9) assms by(fastforce) qed
                  apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(10) assms by(fastforce) qed
                 apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(11) assms by(fastforce) qed
                apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(12) assms by(fastforce) qed
               apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(13) assms by(fastforce) qed
              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(14) assms by(fastforce) qed
             apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(15) assms by(fastforce) qed
            apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(16) assms by(fastforce) qed
           apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(17) assms by(fastforce) qed
                     apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(18) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(19) assms by(fastforce) qed
                   apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(20) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(21) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(22) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(23) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(24) assms by(fastforce) qed
             apply(erule conjE)+
          subgoal premises prems for S proof - show ?thesis using prems(25)  by fastforce qed
             apply(erule conjE)+
          subgoal premises prems for S proof - show ?thesis using prems(25) unfolding holds_forall_hyper_def by fastforce qed
            apply(simp only:eqc2)
            apply(rule seq_extension[where ?R="?PC1"])
             apply(rule cons_prec)
          prefer 2
          apply(rule assign_lockstep)
                   using assms
          unfolding entails_def 
           apply(simp only:conj_def)
          apply(simp only: conj_assoc)
           apply(intro allI impI conjI)
                              apply(erule conjE)+
          subgoal premises prems for S proof - show ?thesis using prems(2) prems(25) prems(10,11) prems(12,13) prems(14-24) assms unfolding holds_forall_hyper_def by fastforce qed
                         apply(erule conjE)+
          subgoal premises prems for S proof - show ?thesis using prems(3) prems(25) prems(10,11) prems(12,13) prems(14-24) assms unfolding holds_forall_hyper_def by fastforce qed
                        apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(4) assms by(fastforce) qed
                       apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(5) assms by(fastforce) qed
                      apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(6) assms by(fastforce) qed
                     apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(7) assms by(fastforce) qed
                    apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(8) assms by(fastforce) qed
                   apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(9) assms by(fastforce) qed
                  apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(10) assms by(fastforce) qed
                           apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(11) assms by(fastforce) qed
                          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(12) assms by(fastforce) qed
                         apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(13) assms by(fastforce) qed
                apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(14) assms by(fastforce) qed
               apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(15) assms by(fastforce) qed
              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(16) assms by(fastforce) qed
             apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(17) assms by(fastforce) qed
            apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(18) assms by(fastforce) qed
           apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(19) assms by(fastforce) qed
                  apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(20) prems(18) prems(14) prems(10) prems(12) assms by(fastforce) qed
                 apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(21)  assms by(fastforce) qed
                apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(22)  assms by(fastforce) qed
               apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(23) prems(19) prems(15) prems(11) prems(13)  assms by(fastforce) qed
              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(24) assms by(fastforce) qed
             apply(erule conjE)+
          subgoal premises prems for S proof - show ?thesis using prems(25) assms unfolding holds_forall_hyper_def by fastforce qed
            apply(rule cons_prec)
             prefer 2
             apply(rule assign_lockstep)
          using assms
          unfolding entails_def 
           apply(intro allI impI conjI)
                          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(2) prems(18,19) assms by(fastforce) qed
                              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(3) prems(18,19) assms apply(auto) 
                        by (smt (verit) plus_ol.simps(1) snd_conv) qed
                                        apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(4) assms by(fastforce) qed
                              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(5) assms by(fastforce) qed
                              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(6) assms by(fastforce) qed
                              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(7) assms by(fastforce) qed
                              apply(erule conjE)+
          subgoal premises prems for S proof - show ?thesis using prems(8) assms prems(18) 
            proof (intro ballI)
              fix  \<sigma>1
              assume asm1:"\<sigma>1 \<in> (if 1 \<in> {1::nat} then {(l, \<sigma>(i := \<sigma> i +\<^sub>o #1)) |l \<sigma>. (l, \<sigma>) \<in> S 1} else S 1)"
              from asm1  obtain \<sigma>1' where fsg:"\<sigma>1' \<in> (S 1)" and fsg2:"\<sigma>1=(fst \<sigma>1', (snd \<sigma>1')(i := (snd \<sigma>1') i +\<^sub>o #1))" by fastforce
              from asm1  prems(18) assms obtain i' where fi:"snd \<sigma>1 i = #i'" by fastforce
              from fsg prems(18) obtain i2' where fi2:"snd \<sigma>1' i = #i2'" by fastforce

              have fis:"snd \<sigma>1 i = snd \<sigma>1' i +\<^sub>o #1" using fsg2 by fastforce
              from prems(8) fsg have fmodi:"snd \<sigma>1' i mod\<^sub>o #4 = #2" by fastforce

              show "snd \<sigma>1 i mod\<^sub>o #4 = #3" using  fi  fi2 fis fmodi 
                apply(auto)
                by presburger
            qed
          qed
                             apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(9) assms by(fastforce) qed
                            apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(10) assms by(fastforce) qed
                           apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(11) assms by(fastforce) qed
                          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(12) prems(18) assms by(fastforce) qed
                         apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(13) assms by(fastforce) qed
                       apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(14) assms by(fastforce) qed
                      apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(15) assms by(fastforce) qed
                     apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(16) assms by(fastforce) qed
                    apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(17) assms by(fastforce) qed
                   apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(18) assms by(fastforce) qed
                  apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(19) assms by(fastforce) qed
                 apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(20) assms by(fastforce) qed
                apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(21) assms by(fastforce) qed
               apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(22) assms by(fastforce) qed
              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(23) assms by(fastforce) qed
             apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(24) assms by(fastforce) qed
            apply(erule conjE)+
          subgoal premises prems for S proof - show ?thesis using prems(25) prems(8) prems(6) prems(18) prems(16) assms unfolding holds_forall_hyper_def 
            proof (intro ballI)
              fix j::nat
              fix  \<sigma>
              assume asm1:"\<sigma> \<in> (if j \<in> {1} then {(l, \<sigma>(i := \<sigma> i +\<^sub>o #1)) |l \<sigma>. (l, \<sigma>) \<in> S j} else S j)"
              assume "j \<in> {1,2::nat}"
              hence "j = 2 \<or> j = 1" by auto
              thus "(if j = 1 then \<lambda>\<sigma>. \<sigma> i <\<^sub>o \<sigma> n else (\<lambda>\<sigma>. \<sigma> i +\<^sub>o #3 <\<^sub>o \<sigma> n)) (snd \<sigma>)"
              proof
                assume "j=2"
                thus ?thesis using prems(25) asm1 unfolding holds_forall_hyper_def by fastforce
              next 
                assume asm2:"j=1"
                from asm1 asm2 obtain \<sigma>' where fsg:"\<sigma>' \<in> (S 1)" and fsg2:"\<sigma>=(fst \<sigma>', (snd \<sigma>')(i := (snd \<sigma>') i +\<^sub>o #1))" by fastforce
                from asm1 asm2 prems(16) assms obtain n' where fn:"snd \<sigma> n = #n'" by fastforce
                from asm1 asm2 prems(18) assms obtain i' where fi:"snd \<sigma> i = #i'" by fastforce
                from fsg prems(16) obtain n2' where fn2:"snd \<sigma>' n = #n2'" by fastforce
                from fsg prems(18) obtain i2' where fi2:"snd \<sigma>' i = #i2'" by fastforce

                have fis:"snd \<sigma> i = snd \<sigma>' i +\<^sub>o #1" using fsg2 by fastforce
                from prems(25) fsg have fle:"snd \<sigma>' i <\<^sub>o snd \<sigma>' n" unfolding holds_forall_hyper_def by fastforce
                from prems(6) fsg have fmodn:"snd \<sigma>' n mod\<^sub>o #4 = #0" by fastforce
                from prems(8) fsg have fmodi:"snd \<sigma>' i mod\<^sub>o #4 = #2" by fastforce
                have fns:"snd \<sigma> n = snd \<sigma>' n" using fsg2 assms by fastforce

                have "snd \<sigma> i <\<^sub>o snd \<sigma> n" using fn fi fn2 fi2 fis fle fmodn fmodi fns
                  apply(auto)
                  by presburger
                thus ?thesis using asm2 by auto
              qed
            qed
          qed
          apply(rule seq_extension[where ?R="?PC3"])
           apply(rule cons_prec)
            prefer 2
          apply(simp only:if_then_else_skip_def)
             apply(rule if_true_lck[where P="?PC2"])
          prefer 2
              apply(simp add:map_comprehension_def hyper_seq_def dom_def)
             prefer 2
        using assms
          unfolding entails_def 
           apply(simp only:conj_def)
          apply(simp only: conj_assoc)
           apply(intro allI impI conjI)
                          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(2) by(fastforce) qed
                         apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(3) by(fastforce) qed
                        apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(4) assms by(fastforce) qed
                       apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(5) assms by(fastforce) qed
                      apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(6) assms by(fastforce) qed
                     apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(7) assms by(fastforce) qed
                    apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(8) assms by(fastforce) qed
                   apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(9) assms by(fastforce) qed
                  apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(10) assms by(fastforce) qed
                 apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(11) assms by(fastforce) qed
                apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(12) assms by(fastforce) qed
               apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(13) assms by(fastforce) qed
              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(14) assms by(fastforce) qed
             apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(15) assms by(fastforce) qed
            apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(16) assms by(fastforce) qed
           apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(17) assms by(fastforce) qed
                     apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(18) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(19) assms by(fastforce) qed
                   apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(20) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(21) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(22) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(23) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(24) assms by(fastforce) qed
             apply(erule conjE)+
          subgoal premises prems for S proof - show ?thesis using prems(25)  by fastforce qed
             apply(erule conjE)+
          subgoal premises prems for S proof - show ?thesis using prems(25) unfolding holds_forall_hyper_def by fastforce qed
            apply(simp only:eqc3)
            apply(rule seq_extension[where ?R="?PC2"])
             apply(rule cons_prec)
          prefer 2
          apply(rule assign_lockstep)
                   using assms
          unfolding entails_def 
           apply(simp only:conj_def)
          apply(simp only: conj_assoc)
           apply(intro allI impI conjI)
                          apply(erule conjE)+
          subgoal premises prems for S proof - show ?thesis using prems(2) prems(25) prems(9,10) prems(12,13) prems(14-24) assms unfolding holds_forall_hyper_def by fastforce qed
                         apply(erule conjE)+
          subgoal premises prems for S proof - show ?thesis using prems(3) prems(25) prems(9,10) prems(12,13) prems(14-24) assms unfolding holds_forall_hyper_def by fastforce qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(4) assms by(fastforce) qed
                       apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(5) assms by(fastforce) qed
                       apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(6) assms by(fastforce) qed
                      apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(7) assms by(fastforce) qed
                     apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(8) assms by(fastforce) qed
                    apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(9) assms by(fastforce) qed
                   apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(10) assms by(fastforce) qed
                  apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(11) assms by(fastforce) qed
                           apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(12) assms by(fastforce) qed
                          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(13) assms by(fastforce) qed
                apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(14) assms by(fastforce) qed
               apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(15) assms by(fastforce) qed
              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(16) assms by(fastforce) qed
             apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(17) assms by(fastforce) qed
            apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(18) assms by(fastforce) qed
           apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(19) assms by(fastforce) qed
                  apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(20) prems(18) prems(14) prems(10) prems(12) assms by(fastforce) qed
                 apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(21)  assms by(fastforce) qed
                apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(22)  assms by(fastforce) qed
               apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(23)   assms by(fastforce) qed
              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(24) prems(19) prems(15) prems(11) prems(13) assms by(fastforce) qed
             apply(erule conjE)+
          subgoal premises prems for S proof - show ?thesis using prems(25) assms unfolding holds_forall_hyper_def by fastforce qed
            apply(rule cons_prec)
             prefer 2
             apply(rule assign_lockstep)
          using assms
          unfolding entails_def 
           apply(intro allI impI conjI)
                          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(2) prems(18,19) assms by(fastforce) qed
                              apply(erule conjE)+
          subgoal premises prems for S proof (simp split: if_splits, intro allI ballI impI)
            fix l 
            fix \<sigma>'::"int_and_list npstate"
            assume "\<exists>\<sigma>. \<sigma>' = \<sigma>(i := \<sigma> i +\<^sub>o #1) \<and> (l, \<sigma>) \<in> S (Suc 0)"
            from this obtain \<sigma> where subeq:"\<sigma>' = \<sigma>(i := \<sigma> i +\<^sub>o #1)" and s1:"(l, \<sigma>) \<in> S (Suc 0)" by blast
            with prems(3) obtain \<sigma>''::"int_and_list nstate" where s2:"\<sigma>''\<in> S 2" and cl:"\<sigma> s = snd \<sigma>'' s \<and>
        \<sigma> x = snd \<sigma>'' x0 +\<^sub>o snd \<sigma>'' x1 +\<^sub>o snd \<sigma>'' x2 +\<^sub>o snd \<sigma>'' x3" and eqimp:"\<sigma> i = snd \<sigma>'' i +\<^sub>o #3 " by auto
            from prems(19) s2 obtain i' where eq1:"snd \<sigma>'' i = #i'" by auto
            from prems(18) s1 obtain i'' where eq2:"\<sigma> i = #i''" by auto
            have f1:"\<sigma>' i = snd \<sigma>'' i +\<^sub>o #4"
              apply(simp only: subeq eqimp eq1)
              by(auto)
            from cl have f2:"\<sigma>' s = snd \<sigma>'' s \<and>
              \<sigma>' x = snd \<sigma>'' x0 +\<^sub>o snd \<sigma>'' x1 +\<^sub>o snd \<sigma>'' x2 +\<^sub>o snd \<sigma>'' x3"
              apply(simp only: subeq)
              using assms
              by(auto)
            from f1 f2 s2 show " \<exists>\<sigma>2\<in>S 2.
              \<sigma>' s = snd \<sigma>2 s \<and>
              \<sigma>' x = snd \<sigma>2 x0 +\<^sub>o snd \<sigma>2 x1 +\<^sub>o snd \<sigma>2 x2 +\<^sub>o snd \<sigma>2 x3 \<and> \<sigma>' i = snd \<sigma>2 i +\<^sub>o #4"
              by auto
            qed
            apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(4) assms by(fastforce) qed
                              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(5) assms by(fastforce) qed
                              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(6) assms by(fastforce) qed
                              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(7) assms by(fastforce) qed
                              apply(erule conjE)+
          subgoal premises prems for S proof - show ?thesis using prems(8) assms prems(18) 
            proof (intro ballI)
              fix  \<sigma>1
              assume asm1:"\<sigma>1 \<in> (if 1 \<in> {1::nat} then {(l, \<sigma>(i := \<sigma> i +\<^sub>o #1)) |l \<sigma>. (l, \<sigma>) \<in> S 1} else S 1)"
              from asm1  obtain \<sigma>1' where fsg:"\<sigma>1' \<in> (S 1)" and fsg2:"\<sigma>1=(fst \<sigma>1', (snd \<sigma>1')(i := (snd \<sigma>1') i +\<^sub>o #1))" by fastforce
              from asm1  prems(18) assms obtain i' where fi:"snd \<sigma>1 i = #i'" by fastforce
              from fsg prems(18) obtain i2' where fi2:"snd \<sigma>1' i = #i2'" by fastforce

              have fis:"snd \<sigma>1 i = snd \<sigma>1' i +\<^sub>o #1" using fsg2 by fastforce
              from prems(8) fsg have fmodi:"snd \<sigma>1' i mod\<^sub>o #4 = #3" by fastforce

              show "snd \<sigma>1 i mod\<^sub>o #4 = #0" using  fi  fi2 fis fmodi 
                apply(auto)
                by presburger
            qed
          qed
                             apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(9) assms by(fastforce) qed
                            apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(10) assms by(fastforce) qed
                           apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(11) assms by(fastforce) qed
                          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(12) prems(18) assms by(fastforce) qed
                         apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(13) assms by(fastforce) qed
                       apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(14) assms by(fastforce) qed
                      apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(15) assms by(fastforce) qed
                     apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(16) assms by(fastforce) qed
                    apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(17) assms by(fastforce) qed
                   apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(18) assms by(fastforce) qed
                  apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(19) assms by(fastforce) qed
                 apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(20) assms by(fastforce) qed
                apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(21) assms by(fastforce) qed
               apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(22) assms by(fastforce) qed
              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(23) assms by(fastforce) qed
             apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(24) assms by(fastforce) qed
           apply(rule cons_prec)
            prefer 2
          apply(rule assign_lockstep)
          using assms
          unfolding entails_def 
           apply(intro allI impI conjI)
                          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(2) assms by force qed
                              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(3) assms by(fastforce) qed
                              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(4) assms by(fastforce) qed
                              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(5) assms by(fastforce) qed
                              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(6) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(7) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(8) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems for S proof - show ?thesis using prems(9) assms 
            proof (intro ballI)
              fix  \<sigma>2
              assume asm1:"\<sigma>2 \<in> (if 2 \<in> {2::nat} then {(l, \<sigma>(i := \<sigma> i +\<^sub>o #4)) |l \<sigma>. (l, \<sigma>) \<in> S 2} else S 2)"
              from asm1  obtain \<sigma>2' where fsg:"\<sigma>2' \<in> (S 2)" and fsg2:"\<sigma>2=(fst \<sigma>2', (snd \<sigma>2')(i := (snd \<sigma>2') i +\<^sub>o #4))" by fastforce
              from asm1  prems(19) assms obtain i' where fi:"snd \<sigma>2 i = #i'" by fastforce
              from fsg prems(19) obtain i2' where fi2:"snd \<sigma>2' i = #i2'" by fastforce

              have fis:"snd \<sigma>2 i = snd \<sigma>2' i +\<^sub>o #4" using fsg2 by fastforce
              from prems(9) fsg have fmodi:"snd \<sigma>2' i mod\<^sub>o #4 = #0" by fastforce

              show "snd \<sigma>2 i mod\<^sub>o #4 = #0" using  fi  fi2 fis fmodi 
                by(auto)
            qed
          qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(10) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(11) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(12) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(13) prems(19) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(14) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(15) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(16) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(17) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(18) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(19) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(20) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(21) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(22) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(23) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(24) assms by(fastforce) qed
          apply(rule cons_post)
           prefer 2
           apply(rule skip_lockstep)
          unfolding entails_def
          apply(simp only:conj_def)
            apply(simp only: conj_assoc)
           apply(intro allI impI conjI)
                          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(1) assms by(fastforce) qed
                         apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(2) assms by(fastforce) qed
                        apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(3) assms by(fastforce) qed
                       apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(4) assms by(fastforce) qed
                      apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(5) assms by(fastforce) qed
                     apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(6) assms by(fastforce) qed
                    apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(7) assms by(fastforce) qed
                   apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(8) assms by(fastforce) qed
                  apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(9) assms by(fastforce) qed
                 apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(10) assms by(fastforce) qed
                apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(11) assms by(fastforce) qed
               apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(12) assms by(fastforce) qed
              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(13) assms by(fastforce) qed
             apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(14) assms by(fastforce) qed
            apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(15) assms by(fastforce) qed
           apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(16) assms by(fastforce) qed
                  apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(17) assms by(fastforce) qed
                 apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(18) assms by(fastforce) qed
                apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(19) assms by(fastforce) qed
               apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(20) assms by(fastforce) qed
              apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(21) assms by(fastforce) qed
             apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(22) assms by(fastforce) qed
            apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(23) assms by(fastforce) qed
          apply(erule conjE)+
          subgoal premises prems for S proof - 
            from prems(1,2,3,4) have H:"\<forall>\<sigma>2\<in>S 2. \<forall>\<sigma>1\<in>S 1. snd \<sigma>1 s = snd \<sigma>2 s \<and> snd \<sigma>1 i = snd \<sigma>2 i" by fastforce
            show ?thesis unfolding low_exp_hyper_def
              apply(intro ballI allI impI)
              apply(auto)
              using prems(2,3) prems(9) apply (metis One_nat_def snd_conv)
              using prems(2,3) prems(9) apply (metis One_nat_def snd_conv)
              using H prems(9,10) prems(15,16,17,18) prems(7) prems(5) apply fastforce
              using H prems(9,10) prems(15,16,17,18) prems(6) prems(4) apply fastforce
              using H prems(9,10) prems(15,16,17,18) prems(6) prems(4) apply fastforce
              using H prems(9,10) prems(15,16,17,18) prems(7) prems(5) apply fastforce
              using prems(4) prems(10) apply (metis snd_conv)
              using prems(4) prems(10) apply (metis snd_conv)
              done
          qed
          done
qed




section \<open>5.2 Nonfixed alignment of loops\<close>

definition next_prime :: "nat \<Rightarrow> nat" where
  "next_prime n = (LEAST p. prime p \<and> p > n)"


abbreviation n_prime_sum :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat, nat) stmt" where
"n_prime_sum i x c n \<equiv>  
  i ::= (\<lambda>s. 0);;
  x ::= (\<lambda>s. 0);;
  c ::= (\<lambda>s. 0);;
  WHILE (\<lambda>s. (s i) < (s n)) DO (
     IF (\<lambda>s. prime (s c)) THEN (
       x ::= (\<lambda>s. (s x) + (s c));;
       i ::= (\<lambda>s. (s i) + 1)
     ) FI;;
    c ::= (\<lambda>s. (s c) + 1)
  )
"


abbreviation n_prime_sum_optimized :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat, nat) stmt" where
"n_prime_sum_optimized i x p n \<equiv>  
  i ::= (\<lambda>s. 0);;
  x ::= (\<lambda>s. 0);;
  p ::= (\<lambda>s. 0);;
  WHILE (\<lambda>s. (s i) < (s n)) DO (
     p ::= (\<lambda>s. (next_prime (s p)));;
     x ::= (\<lambda>s. (s x) + (s p));;
     i ::= (\<lambda>s. (s i) + 1)
    )
"

lemma next_prime_prop:
  "prime (next_prime n) \<and> n < next_prime n"
proof -
  have "\<exists>p::nat. prime p \<and> n < p"
    using bigger_prime[of n] by auto
  then show ?thesis
    unfolding next_prime_def
    by (rule LeastI_ex)
qed

lemma prime_next_prime:
  "prime (next_prime n)"
  using next_prime_prop[of n] by simp

lemma next_prime_gt:
  "n < next_prime n"
  using next_prime_prop[of n] by simp

lemma no_prime_till_next_prime:
  assumes "prime q" "q > n"
  shows "next_prime n \<le> q"
  unfolding next_prime_def
  by (rule Least_le) (use assms in auto)

lemma next_prime_alt:
  assumes "\<forall>c'::nat. n < c' \<and> c' < c \<longrightarrow> \<not> prime c'"
  and "c > n"
  and "prime c"
  shows "c = next_prime n"
  by (meson assms(1,2,3) le_antisym linorder_le_less_linear next_prime_gt no_prime_till_next_prime prime_next_prime)

proposition
  fixes i x c p n::nat
  assumes "distinct [i,x,c,p,n]"
  shows "(\<Turnstile>  {(\<lambda>S::nat hyper_set. (\<forall>\<sigma>1 \<in> (S 1). \<exists>\<sigma>0 \<in> (S 0). (snd \<sigma>0 x) = (snd \<sigma>1 x)) 
                                    \<and> (\<forall>\<sigma>0 \<in> (S 0). \<forall>\<sigma>1 \<in> (S 0). (snd \<sigma>0 n) = (snd \<sigma>1 n))
                                    \<and> (\<forall>\<sigma>0 \<in> (S 1). \<forall>\<sigma>1 \<in> (S 1). (snd \<sigma>0 n) = (snd \<sigma>1 n))
                                    \<and> (\<forall>\<sigma>0 \<in> (S 0). \<forall>\<sigma>1 \<in> (S 1). (snd \<sigma>0 n) = (snd \<sigma>1 n))
)} 
            [[0 \<mapsto> n_prime_sum i x c n, 1 \<mapsto> n_prime_sum_optimized i x p n]::nat hyper_program] 
             {(\<lambda>S::nat hyper_set. \<forall>\<sigma>1 \<in> (S 1). \<exists>\<sigma>0 \<in> (S 0). (snd \<sigma>0 x) = (snd \<sigma>1 x))})"
proof -
  let ?Cs = "[0 \<mapsto> n_prime_sum i x c n, 1 \<mapsto> n_prime_sum_optimized i x p n]::nat hyper_program"
  let ?Cs1 = "[j \<mapsto> i ::= (\<lambda>s. 0) | j \<in> {0,1}]::nat hyper_program"
  let ?Cs2 = "[j \<mapsto> x ::= (\<lambda>s. 0) | j \<in> {0,1}]::nat hyper_program"
  let ?Cs3 = "[j \<mapsto> (if (j=0) then c else p) ::= (\<lambda>s. 0) | j \<in> {0,1}]::nat hyper_program"
  let ?Cs4 = "[ j \<mapsto> WHILE (\<lambda>s. (s i) < (s n)) DO (if (j=0) then (
                         IF (\<lambda>s. prime (s c)) THEN (
                           x ::= (\<lambda>s. (s x) + (s c));;
                           i ::= (\<lambda>s. (s i) + 1)
                         ) FI;;
                        c ::= (\<lambda>s. (s c) + 1)
                     )
                    else (     
                         p ::= (\<lambda>s. (next_prime (s p)));;
                         x ::= (\<lambda>s. (s x) + (s p));;
                         i ::= (\<lambda>s. (s i) + 1)))| j \<in> {0,1}]::nat hyper_program"
  
  let ?Cs4_bodies = "[ j \<mapsto> (if (j=0) then (
                         IF (\<lambda>s. prime (s c)) THEN (
                           x ::= (\<lambda>s. (s x) + (s c));;
                           i ::= (\<lambda>s. (s i) + 1)
                         ) FI;;
                        c ::= (\<lambda>s. (s c) + 1)
                     )
                    else (     
                         p ::= (\<lambda>s. (next_prime (s p)));;
                         x ::= (\<lambda>s. (s x) + (s p));;
                         i ::= (\<lambda>s. (s i) + 1)))| j \<in> {0,1}]::nat hyper_program"
  let ?Cs4_body0 = "[ j \<mapsto> (IF (\<lambda>s. prime (s c)) THEN (
                           x ::= (\<lambda>s. (s x) + (s c));;
                           i ::= (\<lambda>s. (s i) + 1)
                         ) FI;;
                        c ::= (\<lambda>s. (s c) + 1))| j \<in> {0}]::nat hyper_program"
  let ?Cs4_body0p1 = "[ j \<mapsto> IF (\<lambda>s. prime (s c)) THEN (
                           x ::= (\<lambda>s. (s x) + (s c));;
                           i ::= (\<lambda>s. (s i) + 1)
                         ) FI | j \<in> {0}]::nat hyper_program"
  let ?Cs4_body0p2 = "[ j \<mapsto> c ::= (\<lambda>s. (s c) + 1)| j \<in> {0}]::nat hyper_program"
  let ?Cs4_bodiesp1 = "[ j \<mapsto> p ::= (\<lambda>s. (next_prime (s p)))| j \<in> {1}]::nat hyper_program"
  let ?Cs4_bodiesp2 = "[ j \<mapsto> (if (j=0) then (
                         IF (\<lambda>s. prime (s c)) THEN (
                           x ::= (\<lambda>s. (s x) + (s c));;
                           i ::= (\<lambda>s. (s i) + 1)
                         ) FI
                     )
                    else (     
                         x ::= (\<lambda>s. (s x) + (s p));;
                         i ::= (\<lambda>s. (s i) + 1)))| j \<in> {0,1}]::nat hyper_program"
  let ?Cs4_bodiesp3 = "[ j \<mapsto> c ::= (\<lambda>s. (s c) + 1)| j \<in> {0}]::nat hyper_program"
  let ?Cs4_bodiesp2_0 = "[ j \<mapsto> IF (\<lambda>s. prime (s c)) THEN (
                           x ::= (\<lambda>s. (s x) + (s c));;
                           i ::= (\<lambda>s. (s i) + 1)
                         ) FI| j \<in> {0}]::nat hyper_program"
  let ?Cs4_bodiesp2_1 = "[ j \<mapsto> x ::= (\<lambda>s. (s x) + (s p));;
                         i ::= (\<lambda>s. (s i) + 1)| j \<in> {1}]::nat hyper_program"
  let ?Cs4_bodiesp2_0body = "[ j \<mapsto> x ::= (\<lambda>s. (s x) + (s c));;
                           i ::= (\<lambda>s. (s i) + 1) | j \<in> {0}]::nat hyper_program"
  let ?Cs4_bodiesp2p1 = "[ j \<mapsto> x ::= (if (j=0) then (\<lambda>s. (s x) + (s c)) else (\<lambda>s. (s x) + (s p))) | j \<in> {0,1}]::nat hyper_program"
  let ?Cs4_bodiesp2p2 = "[j\<mapsto> i ::= (\<lambda>s. (s i) + 1) | j \<in> {0,1}]::nat hyper_program"

  have eq1: "?Cs = ?Cs1 ;;\<^sub>H ?Cs2 ;;\<^sub>H ?Cs3 ;;\<^sub>H ?Cs4"
    apply(rule)
    by(auto simp add:map_comprehension_def hyper_seq_def)
  have eq2: "?Cs4_body0 = ?Cs4_body0p1 ;;\<^sub>H ?Cs4_body0p2"
    apply(rule)
    by(auto simp add:map_comprehension_def hyper_seq_def)
  have eq3: "?Cs4_bodies = ?Cs4_bodiesp1 ;;\<^sub>H ?Cs4_bodiesp2 ;;\<^sub>H ?Cs4_bodiesp3"
    apply(rule)
    by(auto simp add:map_comprehension_def hyper_seq_def)
  have eq4: "?Cs4_bodiesp2 = ?Cs4_bodiesp2_1 ++ ?Cs4_bodiesp2_0 "
    apply(rule)
    by(auto simp add:map_comprehension_def map_add_def)
  have eq5: "?Cs4_bodiesp2_1 ++ ?Cs4_bodiesp2_0body = ?Cs4_bodiesp2p1 ;;\<^sub>H ?Cs4_bodiesp2p2"
    apply(rule)
    by(auto simp add:map_comprehension_def map_add_def hyper_seq_def)

  let ?P = "(\<lambda>S::nat hyper_set. (\<forall>\<sigma>1 \<in> (S 1). \<exists>\<sigma>0 \<in> (S 0). (snd \<sigma>0 x) = (snd \<sigma>1 x)) 
                                    \<and> (\<forall>\<sigma>0 \<in> (S 0). \<forall>\<sigma>1 \<in> (S 0). (snd \<sigma>0 n) = (snd \<sigma>1 n))
                                    \<and> (\<forall>\<sigma>0 \<in> (S 1). \<forall>\<sigma>1 \<in> (S 1). (snd \<sigma>0 n) = (snd \<sigma>1 n))
                                    \<and> (\<forall>\<sigma>0 \<in> (S 0). \<forall>\<sigma>1 \<in> (S 1). (snd \<sigma>0 n) = (snd \<sigma>1 n)))"
  let ?P1 = "(\<lambda>S::nat hyper_set. (\<forall>\<sigma>1 \<in> (S 1). \<exists>\<sigma>0 \<in> (S 0). (snd \<sigma>0 x) = (snd \<sigma>1 x)) 
                                          \<and>
                 (\<forall>\<sigma>0 \<in> (S 0). \<forall>\<sigma>1 \<in> (S 0). (snd \<sigma>0 i) = (snd \<sigma>1 i) \<and> (snd \<sigma>0 n) = (snd \<sigma>1 n))
                                          \<and>
                 (\<forall>\<sigma>0 \<in> (S 1). \<forall>\<sigma>1 \<in> (S 1). (snd \<sigma>0 i) = (snd \<sigma>1 i) \<and> (snd \<sigma>0 n) = (snd \<sigma>1 n))
                                          \<and>
                 (\<forall>\<sigma>0 \<in> (S 0). \<forall>\<sigma>1 \<in> (S 1). (snd \<sigma>0 i) = (snd \<sigma>1 i) \<and> (snd \<sigma>0 n) = (snd \<sigma>1 n)))"

  let ?Iv = "(\<lambda>m::nat. (\<lambda>S::nat hyper_set. (\<forall>\<sigma>1 \<in> (S 1). \<exists>\<sigma>0 \<in> (S 0). (snd \<sigma>0 x) = (snd \<sigma>1 x))
                                          \<and>
                 (\<forall>\<sigma>0 \<in> (S 0). \<forall>\<sigma>1 \<in> (S 0). (snd \<sigma>0 i) = (snd \<sigma>1 i) \<and> (snd \<sigma>0 n) = (snd \<sigma>1 n))
                                          \<and>
                 (\<forall>\<sigma>0 \<in> (S 1). \<forall>\<sigma>1 \<in> (S 1). (snd \<sigma>0 i) = (snd \<sigma>1 i) \<and> (snd \<sigma>0 n) = (snd \<sigma>1 n))
                                          \<and>
                 (\<forall>\<sigma>0 \<in> (S 0). \<forall>\<sigma>1 \<in> (S 1). (snd \<sigma>0 i) = (snd \<sigma>1 i) \<and> (snd \<sigma>0 n) = (snd \<sigma>1 n))
                                              \<and>
                          (\<forall>\<sigma>0 \<in> (S 0). (snd \<sigma>0 c) = m)
                                              \<and>
                  (\<forall>\<sigma>0 \<in> (S 0). \<forall>\<sigma>1 \<in> (S 1). \<forall>c'. (snd \<sigma>1 p < c' \<and> c' < snd \<sigma>0 c) \<longrightarrow> \<not>(prime c'))
                                              \<and> 
                      (if (m=0) then (\<forall>\<sigma>0 \<in> (S 0). \<forall>\<sigma>1 \<in> (S 1). (snd \<sigma>1 p = snd \<sigma>0 c)) else (\<forall>\<sigma>0 \<in> (S 0). \<forall>\<sigma>1 \<in> (S 1). (snd \<sigma>1 p < snd \<sigma>0 c)))
                  ))"

  let ?P_bodiesp1 = "(\<lambda>m::nat. (\<lambda>S::nat hyper_set. (\<forall>\<sigma>1 \<in> (S 1). \<exists>\<sigma>0 \<in> (S 0). (snd \<sigma>0 x) = (snd \<sigma>1 x))
                                          \<and>
                 (\<forall>\<sigma>0 \<in> (S 0). \<forall>\<sigma>1 \<in> (S 0). (snd \<sigma>0 i) = (snd \<sigma>1 i) \<and> (snd \<sigma>0 n) = (snd \<sigma>1 n))
                                          \<and>
                 (\<forall>\<sigma>0 \<in> (S 1). \<forall>\<sigma>1 \<in> (S 1). (snd \<sigma>0 i) = (snd \<sigma>1 i) \<and> (snd \<sigma>0 n) = (snd \<sigma>1 n))
                                          \<and>
                 (\<forall>\<sigma>0 \<in> (S 0). \<forall>\<sigma>1 \<in> (S 1). (snd \<sigma>0 i) = (snd \<sigma>1 i) \<and> (snd \<sigma>0 n) = (snd \<sigma>1 n))
                                              \<and>
                          (\<forall>\<sigma>0 \<in> (S 0). (snd \<sigma>0 c) = m)
                                              \<and>
                  (\<forall>\<sigma>0 \<in> (S 0). \<forall>\<sigma>1 \<in> (S 1). \<forall>c'. (snd \<sigma>1 p < c' \<and> c' < snd \<sigma>0 c) \<longrightarrow> \<not>(prime c'))
                                             \<and>
                  (\<forall>\<sigma>0 \<in> (S 0). \<forall>\<sigma>1 \<in> (S 1). snd \<sigma>1 p = snd \<sigma>0 c)
                  ))"
  let ?Q = "\<lambda>S::nat hyper_set. (\<forall>\<sigma>1 \<in> (S 1). \<exists>\<sigma>0 \<in> (S 0). (snd \<sigma>0 x) = (snd \<sigma>1 x))"
  let ?V = "\<lambda>J::nat set. if J = {0,1} then (\<lambda>S::nat hyper_set. (\<forall>(\<sigma>0)\<in>(S 0). prime ((snd \<sigma>0) c))) else (
                if J = {0} then (\<lambda>S::nat hyper_set. (\<forall>\<sigma>0\<in>(S 0). \<not>prime ((snd \<sigma>0) c))) else (\<lambda>S::nat hyper_set. False))"

  let ?bodies = "(\<lambda>j. (if (j=0) then (
                       IF (\<lambda>s. prime (s c)) THEN (
                         x ::= (\<lambda>s. (s x) + (s c));;
                         i ::= (\<lambda>s. (s i) + 1)
                       ) FI;;
                      c ::= (\<lambda>s. (s c) + 1)
                   )
                  else (     
                       p ::= (\<lambda>s. (next_prime (s p)));;
                       x ::= (\<lambda>s. (s x) + (s p));;
                       i ::= (\<lambda>s. (s i) + 1))))"
  let ?conds = "(\<lambda>j s. s i < s n)"

  have eq6: "[j\<mapsto>?bodies j|j\<in>{0}] = ?Cs4_body0"
    apply(rule)
    by(auto simp add:map_comprehension_def)


  show ?thesis
    apply(simp only:eq1)
    apply(rule seq_extension[where ?R="?P1"])
     apply(rule cons_prec)
      prefer 2
      apply(rule assign_lockstep)
    using assms
    unfolding entails_def
     apply(intro allI impI conjI)
        apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(2) by(fastforce) qed
       apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(3) by(fastforce) qed
      apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(4) by(fastforce) qed
     apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(5) by(fastforce) qed
    apply(rule seq_extension[where ?R="?P1"])
     apply(rule cons_prec)
      prefer 2
      apply(rule assign_lockstep)
    using assms
    unfolding entails_def
     apply(intro allI impI conjI)
        apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(2) by(fastforce) qed
       apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(3) by(fastforce) qed
      apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(4) by(fastforce) qed
     apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(5) by(fastforce) qed
    apply(rule seq_extension[where ?R="?Iv 0"])
     apply(rule cons_prec)
      prefer 2
      apply(rule assign_lockstep)
    using assms
    unfolding entails_def
     apply(intro allI impI conjI)
          apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(2) assms by(fastforce) qed
         apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(3) assms by(fastforce) qed
        apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(4) assms by(fastforce) qed
       apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(5) assms by(fastforce) qed
      apply(erule conjE)+ subgoal premises prems proof - show ?thesis by(fastforce) qed
      apply(erule conjE)+ subgoal premises prems proof - show ?thesis by(fastforce) qed
    apply(erule conjE)+ subgoal premises prems proof - show ?thesis by(fastforce) qed
    apply(rule cons_post[where Q' = "conj ?Q (holds_forall_hyper {0,1} (lnot_hyper (\<lambda>j. (\<lambda>s. (s i) < (s n)))))"])
     apply (simp add: entail_conj_weaken)
    apply(rule while_nonfixed_lck_sync[where V = "?V" and Q = "?Q" and ?Q_inf="?Q"  and I="{0,1}" and ?bs = "(\<lambda>j. (\<lambda>s. (s i) < (s n)))" and Iv="?Iv"])
  proof -
    show "\<forall>na. \<forall>J\<in>(Pow {0,1} - {{}}). \<Turnstile> { conj (?Iv na) (conj (holds_forall_hyper J ?conds) (?V J))} [[j \<mapsto> (?bodies j) | j \<in> J]] { ?Iv (Suc na) }"
    proof (intro allI ballI)
      fix m 
      fix J ::"nat set"
      assume "J\<in>(Pow {0,1} - {{}})"
      hence "J = {1} \<or> J = {0} \<or> J = {0,1}" by auto
      thus " \<Turnstile> { conj (?Iv m) (conj (holds_forall_hyper J ?conds) (?V J))} [[i \<mapsto> ?bodies i | i \<in> J]] { ?Iv (Suc m) }"
      proof (elim disjE)
        assume "J = {1}"
        show "\<Turnstile> { conj (?Iv m) (conj (holds_forall_hyper J ?conds) (?V J))} [[i \<mapsto> ?bodies i | i \<in> J]] { ?Iv (Suc m) }"
          apply(rule cons_prec[where ?P'="\<lambda>S. False"])
           prefer 2
           apply(rule false)
          apply(intro entailsI)
          unfolding conj_def
          using \<open>J = {1}\<close>
          by(auto)
      next
        assume asm:"J={0}"
        show ?thesis 
          apply(simp only: asm)
          apply(simp only:eq6 eq2)
          apply(rule seq_extension[where ?R="(conj (?Iv m) (holds_forall_hyper {0} (lnot_hyper (\<lambda>j. \<lambda>s. prime (s c)))))"])
           apply(simp only:if_then_else_skip_def)
           apply(rule cons_prec[where ?P'="conj (conj (?Iv m) (holds_forall_hyper {0} (lnot_hyper (\<lambda>j. \<lambda>s. prime (s c))))) (holds_forall_hyper {0} (lnot_hyper (\<lambda>j. \<lambda>s. prime (s c))))"])
          using assms
          unfolding entails_def
            apply(simp only:conj_def)
            apply(simp only:conj_assoc)
            apply(intro allI impI conjI)
                  apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(2) by(fastforce) qed
                 apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(3) by(fastforce) qed
                apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(4) by(fastforce) qed
               apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(5) by(fastforce) qed
              apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(6) by(fastforce) qed
               apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(7) by(fastforce) qed
              apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(8) by(fastforce) qed
             apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(10) unfolding holds_forall_hyper_def lnot_hyper_def by(fastforce) qed
          apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(10) unfolding holds_forall_hyper_def lnot_hyper_def by(fastforce) qed
           apply(rule if_false_lck_simp)
           apply(rule cons_post)
          prefer 2
            apply(rule skip_lockstep)
          using assms
          unfolding entails_def
            apply(simp only:conj_def)
            apply(simp only:conj_assoc)
            apply(intro allI impI conjI)
                  apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(2) by(fastforce) qed
                 apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(3) by(fastforce) qed
                apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(4) by(fastforce) qed
               apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(5) by(fastforce) qed
              apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(6) by(fastforce) qed
            apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(7) by(fastforce) qed
            apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(8) by(fastforce) qed
           apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(9) by(fastforce) qed
          apply(rule cons_prec)
           prefer 2
           apply(rule assign_lockstep)
          using assms
          unfolding entails_def
          apply(simp only:conj_def)
          apply(simp only:conj_assoc)
            apply(intro allI impI conjI)
                  apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(2) assms by(fastforce) qed
                 apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(3) assms  by(fastforce) qed
                apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(4) assms  by(fastforce) qed
               apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(5) assms  by(fastforce) qed
              apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(6) assms  by(fastforce) qed
          apply(erule conjE)+ subgoal premises prems for S proof - 
            have H1:"\<forall>\<sigma>0\<in>if 0 \<in> {0} then {(l, \<sigma>(c := \<sigma> c + 1)) |l \<sigma>. (l, \<sigma>) \<in> S 0} else S 0. snd \<sigma>0 c = Suc m"
              using prems(6) assms  by(fastforce) 
            from prems(7) prems(6) have "\<forall>\<sigma>0\<in>S 0. \<forall>\<sigma>1\<in>S 1. \<forall>c'. snd \<sigma>1 p < c' \<and> c' < m \<longrightarrow> \<not> prime c'" by fastforce
            hence "\<forall>\<sigma>0\<in>if 0 \<in> {0} then {(l, \<sigma>(c := \<sigma> c + 1)) |l \<sigma>. (l, \<sigma>) \<in> S 0} else S 0.
                  \<forall>\<sigma>1\<in>if 1 \<in> {0} then {(l, \<sigma>(c := \<sigma> c + 1)) |l \<sigma>. (l, \<sigma>) \<in> S 1} else S 1. \<forall>c'. snd \<sigma>1 p < c' \<and> c' < m \<longrightarrow> \<not> prime c'"
              using assms
              by auto
            thus ?thesis using H1 prems(6) assms prems(9) unfolding holds_forall_hyper_def lnot_hyper_def
              by (metis (no_types, lifting) One_nat_def less_antisym n_not_Suc_n prems(2) singleton_iff)
          qed
          apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(8) assms  apply(auto) 
              by (metis One_nat_def less_Suc_eq snd_eqD) qed
          done
      next 
        assume asm:"J = {0,1}"
        show ?thesis 
          apply(simp only:asm)
          apply(simp only:eq3)
          apply(rule seq_extension[where ?R="conj (?P_bodiesp1 m) (holds_forall_hyper {0} (\<lambda>j. (\<lambda>s. prime (s c))))"])
           apply(rule cons_prec)
            prefer 2
            apply(rule assign_lockstep)
          using assms
          unfolding entails_def
            apply(simp only:conj_def)
            apply(simp only:conj_assoc)
            apply(intro allI impI conjI)
                  apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(2) assms unfolding next_prime_def apply(auto) by (metis sndI) qed
                 apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(3) assms  by(fastforce) qed
                apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(4) assms  by(fastforce) qed
               apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(5) assms by(fastforce) qed
              apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(6) by(fastforce) qed
            apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(7) assms next_prime_gt  apply(auto)
              by (smt (verit, best) order_less_trans snd_eqD) qed
           apply(erule conjE)+ subgoal premises prems for S proof -
            have H:"\<not>emp (S 0) \<longrightarrow> m>0" using prems(10) prems(6) by(auto simp add:emp_def)
            have "emp (S 0) \<or> \<not>emp (S 0)" by auto
            thus ?thesis
            proof 
              assume "emp (S 0)"
              thus ?thesis by(auto simp add:emp_def)
            next
              assume "\<not>emp (S 0)"
              with H have "m>0" by auto
              with prems(8) have H2:"\<forall>\<sigma>0\<in>S 0. \<forall>\<sigma>1\<in>S 1. snd \<sigma>1 p < snd \<sigma>0 c" by auto
              show ?thesis using prems(7) H2 prems(10) next_prime_alt by fastforce
            qed
          qed
           apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(10) unfolding holds_forall_hyper_def by(fastforce) qed
          apply(simp only:eq4)
          apply(rule seq_extension[where ?R="?P_bodiesp1 m"])
           apply(simp only:if_then_else_skip_def)
           apply(rule if_true_lck)
            prefer 2
          apply(simp add:map_comprehension_def dom_def)
           apply(simp only:eq5)
           apply(rule seq_extension[where ?R="?P_bodiesp1 m"])
            apply(rule cons_prec)
          prefer 2
             apply(rule assign_lockstep)
          using assms
          unfolding entails_def
            apply(simp only:conj_def)
            apply(simp only:conj_assoc)
            apply(intro allI impI conjI)
                  apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(2) prems(8) assms by fastforce qed
                 apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(3) assms  by(fastforce) qed
                apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(4) assms  by(fastforce) qed
               apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(5) assms by(fastforce) qed
              apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(6) assms by(fastforce) qed
            apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(7) assms by fastforce qed
            apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(8) assms by fastforce qed
           apply(rule cons_prec)
            prefer 2
            apply(rule assign_lockstep)
          using assms
          unfolding entails_def
           apply(intro allI impI conjI)
                  apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(2) assms by fastforce qed
                 apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(3) assms  by(fastforce) qed
                apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(4) assms  by(fastforce) qed
               apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(5) assms by(fastforce) qed
              apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(6) assms by(fastforce) qed
            apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(7) assms by fastforce qed
           apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(8) assms by fastforce qed
          apply(rule cons_prec)
           prefer 2
           apply(rule assign_lockstep)
          using assms
          unfolding entails_def
           apply(intro allI impI conjI)
                  apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(2) assms by fastforce qed
                 apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(3) assms  by(fastforce) qed
                apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(4) assms  by(fastforce) qed
               apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(5) assms by(fastforce) qed
              apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(6) assms by(fastforce) qed
            apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(7) prems(8) assms by fastforce qed
          apply(erule conjE)+ subgoal premises prems proof - show ?thesis using prems(8) assms by fastforce qed
          done
      qed
    qed
  next
    show "(progress_side_condition2_sync ?Iv {0,1} ?conds ?V)" 
    proof
      fix m::nat
      from bigger_prime obtain m' where "m \<le> m'" and "prime m'" 
        using order_less_imp_le by blast
      show "\<forall>i\<in>{0,1}. \<exists>n'\<ge>m. (entails (?Iv n') (disj (\<lambda>S. (holds_forall (lnot (?conds i)) (S i))) (disj_I ({J . J \<in> Pow {0,1} \<and> i \<in> J}) (\<lambda>J. conj (holds_forall_hyper J ?conds) (?V J)))))"
        unfolding disj_def disj_I_def
      proof(intro allI ballI impI entailsI conjI exI)
        from \<open>m \<le> m'\<close> show "m \<le> m'" by auto
      next
        fix i'::nat
        fix S'::"nat hyper_set"
        assume "?Iv m' S'" and "i' \<in> {0, 1}"
        show "(holds_forall (lnot (\<lambda>s. s i < s n))) (S' i') \<or>
            (\<exists>ia\<in>{J \<in> Pow {0, 1}. i' \<in> J}.
                Logic.conj (holds_forall_hyper ia (\<lambda>j s. s i < s n))
                 (if ia = {0, 1} then \<lambda>S. \<forall>\<sigma>0\<in>S 0. prime (snd \<sigma>0 c)
                  else if ia = {0} then \<lambda>S. \<forall>\<sigma>0\<in>S 0. \<not> prime (snd \<sigma>0 c) else (\<lambda>S. False))
                 S')"
          apply(subst disj_imp)
          apply(intro impI)
        proof -
        assume hfa:"\<not> holds_forall (lnot (\<lambda>s. s i < s n)) (S' i')"
        from \<open>?Iv m' S'\<close> hfa have H1: "(holds_forall_hyper {0,1} (\<lambda>j s. s i < s n)) S'" 
          unfolding holds_forall_hyper_def holds_forall_def lnot_def holds_forall_hyper_def
          using \<open>i' \<in> {0, 1}\<close>
          by (metis empty_iff insert_iff)
        from \<open>?Iv m' S'\<close>  \<open>prime m'\<close> have H2: "\<forall>\<sigma>0\<in>S' 0. prime (snd \<sigma>0 c)" by fastforce
        show "\<exists>ia\<in>{J \<in> Pow {0, 1}. i' \<in> J}.
       Logic.conj (holds_forall_hyper ia (\<lambda>j s. s i < s n))
        (if ia = {0, 1} then \<lambda>S. \<forall>\<sigma>0\<in>S 0. prime (snd \<sigma>0 c)
         else if ia = {0} then \<lambda>S. \<forall>\<sigma>0\<in>S 0. \<not> prime (snd \<sigma>0 c) else (\<lambda>S. False))
        S'"
        proof -
          have "i' \<in> {0,1} \<and> conj (holds_forall_hyper {0,1} (\<lambda>j s. s i < s n))
          (if {0,1} = {0, 1} then \<lambda>S. \<forall>\<sigma>0\<in>S 0. prime (snd \<sigma>0 c) else if {0,1} = {0} then \<lambda>S. \<forall>\<sigma>0\<in>S 0. \<not> prime (snd \<sigma>0 c) else (\<lambda>S. False)) S'"
            using H1 H2 \<open>i' \<in> {0,1}\<close>
            by(auto simp add:conj_def)
          thus ?thesis
            by blast
        qed
      qed
    qed
  qed
  next
    show "(progress_side_condition1_sync ?Iv {0,1} ?conds ?V)" 
    proof(intro allI entailsI)
      fix m S
      assume asm:"?Iv m S"
      from asm have "(\<forall>\<sigma>0\<in>S 0. \<not>(snd \<sigma>0 i < snd \<sigma>0 n)) \<and> (\<forall>\<sigma>1\<in>S 1. \<not>(snd \<sigma>1 i < snd \<sigma>1 n)) \<or> (\<forall>\<sigma>0\<in>S 0. (snd \<sigma>0 i < snd \<sigma>0 n)) \<and> (\<forall>\<sigma>1\<in>S 1. (snd \<sigma>1 i < snd \<sigma>1 n))"
        by metis
      thus "(disj (disj_I (Pow {0,1} - {{}}) (\<lambda>J. conj (holds_forall_hyper J ?conds) (?V J))) (holds_forall_hyper {0,1} (lnot_hyper ?conds))) S"
      proof
        assume asm:"(\<forall>\<sigma>0\<in>S 0. \<not>(snd \<sigma>0 i < snd \<sigma>0 n)) \<and> (\<forall>\<sigma>1\<in>S 1. \<not>(snd \<sigma>1 i < snd \<sigma>1 n))"
        show ?thesis
          unfolding disj_def
          apply (rule disjI2)
          unfolding holds_forall_hyper_def lnot_hyper_def
          using asm
          by(auto)
      next
        assume asm1: "(\<forall>\<sigma>0\<in>S 0. snd \<sigma>0 i < snd \<sigma>0 n) \<and> (\<forall>\<sigma>1\<in>S 1. snd \<sigma>1 i < snd \<sigma>1 n)"
        from asm have "(\<forall>\<sigma>0\<in>S 0. prime ((snd \<sigma>0) c)) \<or> (\<forall>\<sigma>0\<in>S 0. \<not>prime ((snd \<sigma>0) c))" by auto
        thus ?thesis
        proof(rule)
          assume asm2: "\<forall>\<sigma>0\<in>S 0. prime (snd \<sigma>0 c)"
          with asm1 have "(\<forall>\<sigma>0\<in>S 0. snd \<sigma>0 i < snd \<sigma>0 n) \<and> (\<forall>\<sigma>1\<in>S 1. snd \<sigma>1 i < snd \<sigma>1 n) \<and> (\<forall>\<sigma>0\<in>S 0. prime (snd \<sigma>0 c))" by auto
          show ?thesis unfolding disj_def disj_I_def conj_def holds_forall_hyper_def holds_forall_hyper_def
            apply (rule disjI1)
          proof
            from asm1 asm2 show "(\<forall>ia\<in>{0,1}. \<forall>\<phi>\<in>S ia. snd \<phi> i < snd \<phi> n) \<and> (if {0,1} = {0, 1} then \<lambda>S. \<forall>\<sigma>0\<in>S 0. prime (snd \<sigma>0 c) else if {0,1} = {0} then \<lambda>S. \<forall>\<sigma>0\<in>S 0. \<not> prime (snd \<sigma>0 c) else (\<lambda>S. False)) S"
              by simp
          next 
            show "{0, 1} \<in> Pow {0, 1} - {{}}" by auto
          qed
        next
          assume asm2: "\<forall>\<sigma>0\<in>S 0. \<not> prime (snd \<sigma>0 c)"
          with asm1 have "(\<forall>\<sigma>1\<in>S 1. snd \<sigma>1 i < snd \<sigma>1 n) \<and> (\<forall>\<sigma>0\<in>S 0. \<not>prime (snd \<sigma>0 c))" by auto
          show ?thesis unfolding disj_def disj_I_def conj_def holds_forall_hyper_def holds_forall_hyper_def
            apply (rule disjI1)
          proof
            from asm1 asm2 show "(\<forall>ia\<in>{0::nat}. \<forall>\<phi>\<in>S ia. snd \<phi> i < snd \<phi> n) \<and> (if {0::nat} = {0, 1} then \<lambda>S. \<forall>\<sigma>0\<in>S 0. prime (snd \<sigma>0 c) else if {0} = {0} then \<lambda>S. \<forall>\<sigma>0\<in>S 0. \<not> prime (snd \<sigma>0 c) else (\<lambda>S. False)) S"
              by(auto)
          next
            show "{0} \<in> Pow {0, 1} - {{}}" by auto
          qed
        qed
      qed
    qed
  next
    show "\<forall>na. \<Turnstile> { (?Iv na)} [[i \<mapsto> Assume (lnot (?conds i)) | i \<in> {0,1}]] { ?Q }" 
      apply(intro allI)
      apply(rule cons_prec[where ?P'="(\<lambda>S::nat hyper_set. (\<forall>\<sigma>1 \<in> (S 1). \<exists>\<sigma>0 \<in> (S 0). (snd \<sigma>0 x) = (snd \<sigma>1 x) \<and> (snd \<sigma>0 i) = (snd \<sigma>1 i) \<and> (snd \<sigma>0 n) = (snd \<sigma>1 n)))"])
       apply(intro entailsI)
       apply fastforce
      apply(rule cons_prec)
      prefer 2
       apply(rule assume_lockstep)
      apply(intro entailsI)
      unfolding lnot_def
      by fastforce
  next 
    show "relational_upwards_closed {0, 1} (\<lambda>n. ?Q) ?Q" 
      apply(auto simp add:relational_upwards_closed_def hyper_union_def hyper_ascending_def hyper_set_le_def)
      by (metis snd_eqD)
  next
    show "{0, 1} \<noteq> {}" by auto
  qed
qed






section \<open>5.3 \<exists>\<forall> properties\<close>

abbreviation index_access where
"index_access x i s \<equiv> (IF (\<lambda>\<sigma>. \<sigma> i \<ge>\<^sub>o #0 \<and> \<sigma> i \<le>\<^sub>o ((len (\<sigma> s)) -\<^sub>o #1)) 
            THEN 
              x ::= (\<lambda>\<sigma>. (\<sigma> s) !\<^sub>o (\<sigma> i))
            FI)::(nat,int_and_list) stmt"


abbreviation index_access_buggy where
"index_access_buggy x i s \<equiv> (IF (\<lambda>\<sigma>. \<sigma> i \<ge>\<^sub>o #0 \<and> \<sigma> i <\<^sub>o ((len (\<sigma> s)) -\<^sub>o #1)) 
            THEN 
              x ::= (\<lambda>\<sigma>. (\<sigma> s) !\<^sub>o (\<sigma> i))
            FI)::(nat,int_and_list) stmt"


lemma not_there:"\<exists>y::int. [0] ! 0 \<noteq> y"
  by presburger


text\<open>IMPORTANT: Most of the assertions contain additional typing formulas
                compared to the version presented in the report.
                This is because we implement a simple type-system and need to always keep around 
                the information about which variable is of what type. 
                We did not want to present this purely technical aspect of the proof.\<close>
proposition 
  fixes s x i :: nat
  assumes vars_distinct : "distinct [s, x, i]"
  shows  "\<Turnstile> {(\<lambda>S::int_and_list hyper_set.  (\<exists>\<sigma>2\<in>(S 2). (snd \<sigma>2 s) !\<^sub>o ((len (snd \<sigma>2 s))-\<^sub>o #1) \<noteq> (snd \<sigma>2 x))
             \<and> (\<forall>\<sigma>2\<in>(S 1). \<forall>\<sigma>1\<in>(S 1). snd \<sigma>1 s = snd \<sigma>2 s \<and> snd \<sigma>1 i = snd \<sigma>2 i)
              \<and> (\<forall>\<sigma>2\<in>(S 2). \<forall>\<sigma>1\<in>(S 2). snd \<sigma>1 s = snd \<sigma>2 s \<and> snd \<sigma>1 i = snd \<sigma>2 i)
              \<and> (\<forall>\<sigma>1\<in>(S 1). \<forall>\<sigma>2\<in>(S 2). snd \<sigma>1 s = snd \<sigma>2 s \<and> snd \<sigma>1 i = snd \<sigma>2 i)
              \<and> (\<forall>\<sigma>1\<in>(S 1). (snd \<sigma>1 i) = (len (snd \<sigma>1 s)) -\<^sub>o #1 \<and> (snd \<sigma>1 i) \<ge>\<^sub>o #0)
              \<and> (\<forall>\<sigma>2\<in>(S 2). (snd \<sigma>2 i) = (len (snd \<sigma>2 s)) -\<^sub>o #1 \<and> (snd \<sigma>2 i) \<ge>\<^sub>o #0)
              \<and> (\<forall>\<sigma>1\<in>(S 1). \<exists>xs::int list. snd \<sigma>1 s = ListV xs) \<and> (\<forall>\<sigma>2\<in>(S 2). \<exists>xs::int list. snd \<sigma>2 s = ListV xs)
              \<and> (\<forall>\<sigma>1\<in>(S 1). \<exists>i'::int. snd \<sigma>1 i = IntV i') \<and> (\<forall>\<sigma>2\<in>(S 2). \<exists>i'::int. snd \<sigma>2 i = IntV i')
       )} 
    [[1 \<mapsto> index_access x i s, 2 \<mapsto> index_access_buggy x i s]::int_and_list hyper_program] 
     {\<lambda>S::int_and_list hyper_set. (\<exists>\<sigma>2\<in>(S 2). \<forall>\<sigma>1\<in>(S 1). snd \<sigma>1 x \<noteq> snd \<sigma>2 x)}"
proof-
  let ?P="(\<lambda>S::int_and_list hyper_set.  (\<exists>\<sigma>2\<in>(S 2). (snd \<sigma>2 s) !\<^sub>o ((len (snd \<sigma>2 s))-\<^sub>o #1) \<noteq> (snd \<sigma>2 x))
             \<and> (\<forall>\<sigma>2\<in>(S 1). \<forall>\<sigma>1\<in>(S 1). snd \<sigma>1 s = snd \<sigma>2 s \<and> snd \<sigma>1 i = snd \<sigma>2 i)
              \<and> (\<forall>\<sigma>2\<in>(S 2). \<forall>\<sigma>1\<in>(S 2). snd \<sigma>1 s = snd \<sigma>2 s \<and> snd \<sigma>1 i = snd \<sigma>2 i)
              \<and> (\<forall>\<sigma>1\<in>(S 1). \<forall>\<sigma>2\<in>(S 2). snd \<sigma>1 s = snd \<sigma>2 s \<and> snd \<sigma>1 i = snd \<sigma>2 i)
              \<and> (\<forall>\<sigma>1\<in>(S 1). (snd \<sigma>1 i) = (len (snd \<sigma>1 s)) -\<^sub>o #1 \<and> (snd \<sigma>1 i) \<ge>\<^sub>o #0)
              \<and> (\<forall>\<sigma>2\<in>(S 2). (snd \<sigma>2 i) = (len (snd \<sigma>2 s)) -\<^sub>o #1 \<and> (snd \<sigma>2 i) \<ge>\<^sub>o #0)
              \<and> (\<forall>\<sigma>1\<in>(S 1). \<exists>xs::int list. snd \<sigma>1 s = ListV xs) \<and> (\<forall>\<sigma>2\<in>(S 2). \<exists>xs::int list. snd \<sigma>2 s = ListV xs)
              \<and> (\<forall>\<sigma>1\<in>(S 1). \<exists>i'::int. snd \<sigma>1 i = IntV i') \<and> (\<forall>\<sigma>2\<in>(S 2). \<exists>i'::int. snd \<sigma>2 i = IntV i')
       )"
  let ?bs = "(\<lambda>j::nat. (if (j = 1) then (\<lambda>\<sigma>. \<sigma> i \<ge>\<^sub>o #0 \<and> \<sigma> i \<le>\<^sub>o ((len (\<sigma> s)) -\<^sub>o #1)) else (\<lambda>\<sigma>. \<sigma> i \<ge>\<^sub>o #0 \<and> \<sigma> i <\<^sub>o ((len (\<sigma> s)))-\<^sub>o#1)))"
  let ?Cs = "[1 \<mapsto> index_access x i s, 2 \<mapsto> index_access_buggy x i s]::int_and_list hyper_program"
  let ?Cs' = "[j \<mapsto> (IF (?bs j)
            THEN 
              (x ::= (\<lambda>\<sigma>. (\<sigma> s) !\<^sub>o (\<sigma> i)))
            ELSE 
              (Skip))| j \<in> {1,2}]"
  have eq: "?Cs = ?Cs'"
    apply(rule)
    by(auto simp add:map_comprehension_def fun_upd_def if_then_else_skip_def)

  have eq2: "pick_branch (conj ?P  (conj (\<lambda>S. holds_forall (lnot (?bs 2))(S 2)) (\<lambda>S. holds_forall (?bs 1) (S 1)))) ?bs (\<lambda>j. (x ::= (\<lambda>\<sigma>. (\<sigma> s) !\<^sub>o (\<sigma> i)))) (\<lambda>j. Skip) (2::nat)
            = Skip"
    apply(simp)
    unfolding entails_def
    apply(simp only:not_all not_imp)
    apply(simp only:conj_def)
    apply(simp only:conj_assoc)
  proof -
    from not_there obtain x'::int where xorg:"[0] ! 0 \<noteq> x'" by blast
    let ?l = "\<lambda>v. #0"
    let ?\<sigma> = "\<lambda>v. (if (v=s) then (ListV [0]) else (if (v=i) then #0 else (if (v=x) then #x' else #0)))"
    let ?S = "(\<lambda>n. (if (n=1) then {(?l, ?\<sigma>)} else {(?l, ?\<sigma>)}))::int_and_list hyper_set"
    show "\<exists>S::int_and_list hyper_set. (\<exists>\<sigma>2\<in>S 2. snd \<sigma>2 s !\<^sub>o (len (snd \<sigma>2 s) -\<^sub>o #1) \<noteq> snd \<sigma>2 x) \<and>
        (\<forall>\<sigma>2\<in>S (Suc 0). \<forall>\<sigma>1\<in>S (Suc 0). snd \<sigma>1 s = snd \<sigma>2 s \<and> snd \<sigma>1 i = snd \<sigma>2 i) \<and>
        (\<forall>\<sigma>2\<in>S 2. \<forall>\<sigma>1\<in>S 2. snd \<sigma>1 s = snd \<sigma>2 s \<and> snd \<sigma>1 i = snd \<sigma>2 i) \<and>
        (\<forall>\<sigma>1\<in>S (Suc 0). \<forall>\<sigma>2\<in>S 2. snd \<sigma>1 s = snd \<sigma>2 s \<and> snd \<sigma>1 i = snd \<sigma>2 i) \<and>
        (\<forall>\<sigma>1\<in>S (Suc 0). snd \<sigma>1 i = len (snd \<sigma>1 s) -\<^sub>o #1 \<and> snd \<sigma>1 i \<ge>\<^sub>o #0) \<and>
        (\<forall>\<sigma>2\<in>(S 2). (snd \<sigma>2 i) = (len (snd \<sigma>2 s)) -\<^sub>o #1 \<and> (snd \<sigma>2 i) \<ge>\<^sub>o #0) \<and> 
        (\<forall>\<sigma>1\<in>S (Suc 0). \<exists>xs. snd \<sigma>1 s = ListV xs) \<and>
        (\<forall>\<sigma>2\<in>S 2. \<exists>xs. snd \<sigma>2 s = ListV xs) \<and>
        (\<forall>\<sigma>1\<in>S (Suc 0). \<exists>i'. snd \<sigma>1 i = #i') \<and>
        (\<forall>\<sigma>2\<in>S 2. \<exists>i'. snd \<sigma>2 i = #i') \<and>
        holds_forall (lnot (\<lambda>\<sigma>. \<sigma> i \<ge>\<^sub>o #0 \<and> \<sigma> i <\<^sub>o len (\<sigma> s) -\<^sub>o #1)) (S 2) \<and>
        holds_forall (\<lambda>\<sigma>. \<sigma> i \<ge>\<^sub>o #0 \<and> \<sigma> i \<le>\<^sub>o len (\<sigma> s) -\<^sub>o #1) (S (Suc 0)) \<and> \<not> holds_forall (\<lambda>\<sigma>. \<sigma> i \<ge>\<^sub>o #0 \<and> \<sigma> i <\<^sub>o len (\<sigma> s) -\<^sub>o #1) (S 2)"
      apply(rule exI[where x = "?S"])
      apply(intro conjI)
      subgoal premises prems proof - show ?thesis using assms xorg by(auto) qed
      subgoal premises prems proof - show ?thesis by(auto) qed
      subgoal premises prems proof - show ?thesis by(auto) qed
      subgoal premises prems proof - show ?thesis using assms by(auto) qed
      subgoal premises prems proof - show ?thesis using assms by(auto) qed
      subgoal premises prems proof - show ?thesis using assms by(auto simp add:emp_def) qed
      subgoal premises prems proof - show ?thesis using assms by(auto) qed
      subgoal premises prems proof - show ?thesis using assms by(auto) qed
      subgoal premises prems proof - show ?thesis using assms by(auto) qed
      subgoal premises prems proof - show ?thesis using assms by(auto) qed
      subgoal premises prems proof - show ?thesis using assms by(auto simp add:holds_forall_def lnot_def) qed
      subgoal premises prems proof - show ?thesis using assms by(auto simp add:holds_forall_def)  qed
      subgoal premises prems proof - show ?thesis using assms by(auto simp add:holds_forall_def)  qed
      done
  qed

  have eq3: "pick_branch (conj ?P  (conj (\<lambda>S. holds_forall (lnot (?bs 2)) (S 2)) (\<lambda>S. holds_forall ((?bs 1)) (S 1)))) ?bs (\<lambda>j. (x ::= (\<lambda>\<sigma>. (\<sigma> s) !\<^sub>o (\<sigma> i)))) (\<lambda>j. Skip) (1::nat)
            = (x ::= (\<lambda>\<sigma>. (\<sigma> s) !\<^sub>o (\<sigma> i)))"
    apply(simp)
    unfolding entails_def
    apply(simp only:conj_def)
    apply(simp only:conj_assoc)
    apply(intro allI impI)
            apply(erule conjE)+
    subgoal premises prems proof - show ?thesis using prems(12) by(fastforce) qed
    done

  have eq4: "[j \<mapsto> 
    (pick_branch (conj ?P  (conj (\<lambda>S. holds_forall (lnot (?bs 2)) (S 2)) (\<lambda>S. holds_forall ((?bs 1)) (S 1)))) ?bs (\<lambda>j. (x ::= (\<lambda>\<sigma>. (\<sigma> s) !\<^sub>o (\<sigma> i)))) (\<lambda>j. Skip) j) | j \<in> {1,2}]
      = ([j \<mapsto> (if (j = 2) then Skip else (x ::= (\<lambda>\<sigma>. (\<sigma> s) !\<^sub>o (\<sigma> i)))) | j \<in> {1::nat, 2}]::int_and_list hyper_program)"
    apply(rule)
    using eq2 eq3
    by(auto simp add:map_comprehension_def map_add_def eq2 eq3)

  have eq5: "[j \<mapsto> (if (j = 2) then Skip else (x ::= (\<lambda>\<sigma>. (\<sigma> s) !\<^sub>o (\<sigma> i)))) | j \<in> {1::nat, 2}] 
           = ([j \<mapsto> Skip | j \<in> {2::nat}]::int_and_list hyper_program) ++ ([j \<mapsto> (x ::= (\<lambda>\<sigma>. (\<sigma> s) !\<^sub>o (\<sigma> i))) | j \<in> {1}]::int_and_list hyper_program)"
    apply(rule)
    by(auto simp add:map_comprehension_def map_add_def)

  show ?thesis
    apply(rule cons_prec[where ?P'="conj ?P  (conj (\<lambda>S. holds_forall (lnot (?bs 2)) (S 2)) (\<lambda>S. holds_forall ((?bs 1)) (S 1)))"])
    using assms
    unfolding entails_def 
     apply(simp only:conj_def)
     apply(simp only:conj_assoc)
     apply(intro allI impI conjI)
            apply(erule conjE)+
    subgoal premises prems proof - show ?thesis using prems(2) by(fastforce) qed
           apply(erule conjE)+
    subgoal premises prems proof - show ?thesis using prems(3) by(fastforce) qed
    apply(erule conjE)+
    subgoal premises prems proof - show ?thesis using prems(4) by(fastforce) qed
         apply(erule conjE)+
    subgoal premises prems proof - show ?thesis using prems(5) by(fastforce) qed
        apply(erule conjE)+
    subgoal premises prems proof - show ?thesis using prems(6) by(fastforce) qed
       apply(erule conjE)+
    subgoal premises prems proof - show ?thesis using prems(7) by(fastforce) qed
      apply(erule conjE)+
    subgoal premises prems proof - show ?thesis using prems(8) by(fastforce) qed
     apply(erule conjE)+
    subgoal premises prems proof - show ?thesis using prems(9) by(fastforce) qed
     apply(erule conjE)+
    subgoal premises prems proof - show ?thesis using prems(10) by(fastforce) qed
       apply(erule conjE)+
    subgoal premises prems proof - show ?thesis using prems(11) by(fastforce) qed
     apply(erule conjE)+
    subgoal premises prems for S proof - show ?thesis using prems(7) prems(9) prems(11) unfolding holds_forall_def lnot_def by auto qed
     apply(erule conjE)+
    subgoal premises prems proof - show ?thesis using prems(3) prems(6) prems(7) prems(8) unfolding holds_forall_def  by(fastforce) qed
    apply(simp only:eq)
    apply(rule if_sync_lck_arb_simp)
    subgoal premises prems proof(intro ballI)
      fix j::nat
      assume "j \<in> {1, 2}"
      hence "j = 1 \<or> j = 2" by auto
      thus "(entails
          (conj ?P  (conj (\<lambda>S. holds_forall (lnot(?bs 2)) (S 2)) (\<lambda>S. holds_forall ( (?bs 1)) (S 1)))) (\<lambda>S. holds_forall (?bs j) (S j)))
           \<or> (entails
          (conj ?P  (conj (\<lambda>S. holds_forall (lnot(?bs 2)) (S 2)) (\<lambda>S. holds_forall ( (?bs 1)) (S 1)))) (\<lambda>S. holds_forall (lnot (?bs j)) (S j)))" 
      proof
        assume asm:"j=1"
        show "(entails
          (conj ?P  (conj (\<lambda>S. holds_forall (lnot(?bs 2)) (S 2)) (\<lambda>S. holds_forall ( (?bs 1)) (S 1)))) (\<lambda>S. holds_forall (?bs j) (S j)))
           \<or> (entails
          (conj ?P  (conj (\<lambda>S. holds_forall (lnot(?bs 2)) (S 2)) (\<lambda>S. holds_forall ( (?bs 1)) (S 1)))) (\<lambda>S. holds_forall (lnot (?bs j)) (S j)))" 
          apply(rule disjI1)
          using assms
          unfolding entails_def 
          apply(simp only:conj_def)
          apply(simp only:conj_assoc)
          apply(intro allI impI conjI)
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(13) asm by(fastforce) qed
          done
      next
        assume asm:"j=2"
        show "(entails
          (conj ?P  (conj (\<lambda>S. holds_forall (lnot(?bs 2)) (S 2)) (\<lambda>S. holds_forall ( (?bs 1)) (S 1)))) (\<lambda>S. holds_forall (?bs j) (S j)))
           \<or> (entails
          (conj ?P  (conj (\<lambda>S. holds_forall (lnot(?bs 2)) (S 2)) (\<lambda>S. holds_forall ( (?bs 1)) (S 1)))) (\<lambda>S. holds_forall (lnot (?bs j)) (S j)))" 
          apply(rule disjI2)
          using assms
          unfolding entails_def 
          apply(simp only:conj_def)
          apply(simp only:conj_assoc)
          apply(intro allI impI conjI)
          apply(erule conjE)+
          subgoal premises prems proof - show ?thesis using prems(12) asm by(fastforce) qed
          done
      qed
    qed
    apply(simp only:eq4)
    apply(simp only:eq5)
    apply(rule rel_extension[where ?R="(conj ?P  (conj (\<lambda>S. holds_forall (lnot(?bs 2)) (S 2)) (\<lambda>S. holds_forall ( (?bs 1)) (S 1))))"])
      apply(rule skip_lockstep)
     prefer 2
     apply(simp add:map_comprehension_def dom_def)
    apply(rule cons_prec)
    prefer 2
    apply(rule assign_lockstep)
    using assms
    unfolding entails_def 
     apply(simp only:conj_def)
     apply(simp only:conj_assoc)
     apply(intro allI impI conjI)
            apply(erule conjE)+
    subgoal premises prems proof - show ?thesis using prems(2) apply(auto)
        using prems(3,4,5,6)
        by (metis fun_upd_same numeral_1_eq_Suc_0 numeral_One prems(7) snd_eqD) qed
    done
qed




section \<open>Mini case study\<close>

abbreviation four_to_hundred :: "nat \<Rightarrow> nat \<Rightarrow> (nat, nat) stmt" where
"four_to_hundred i x \<equiv>  
  i ::= (\<lambda>s. 100);;
  x ::= (\<lambda>s. 1);;
  WHILE (\<lambda>s. (s i) > 0) DO (
     x ::= (\<lambda>s. 4*(s x));;
     i ::= (\<lambda>s. (s i) - 1)
    )
"


abbreviation four_to_hundred_primes :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat, nat) stmt" where
"four_to_hundred_primes i x c \<equiv>  
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
            [[0 \<mapsto> four_to_hundred i x, 1 \<mapsto> four_to_hundred_primes i x c]::nat hyper_program] 
             {(\<lambda>S::nat hyper_set. \<forall>\<sigma>0 \<in> (S 0). \<exists>\<sigma>1 \<in> (S 1). (snd \<sigma>0 x) = (snd \<sigma>1 x))})"
proof -
  let ?Cs = "[0 \<mapsto> four_to_hundred i x, 1 \<mapsto> four_to_hundred_primes i x c]::nat hyper_program"
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
  proof(rule seq_extension[where ?R = "?Iv_p1"])
    have eq1: "[0 \<mapsto> i ::= (\<lambda>s. 100), 1 \<mapsto> i ::= (\<lambda>s. 100)] = [j \<mapsto> (\<lambda>j. i ::= (\<lambda>s. 100)) j | j \<in> {0,1}]"
      apply(rule)
      by(auto simp add:map_comprehension_def)
    show "\<Turnstile> {(\<lambda>S::nat hyper_set. \<forall>\<sigma>0 \<in> (S 0). \<exists>\<sigma>1 \<in> (S 1). (snd \<sigma>0 x) = (snd \<sigma>1 x))} 
                  [[0 \<mapsto> i ::= (\<lambda>s. 100),1 \<mapsto> i ::= (\<lambda>s. 100)]] 
             {?Iv_p1}"
    apply(simp only:eq1)
    apply(rule cons_prec)
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
    proof (rule seq_extension[where ?R = "?Iv_p1"])
      have eq2: "[0 \<mapsto> x ::= (\<lambda>s. 1), 1 \<mapsto> x ::= (\<lambda>s. 1)] = [j \<mapsto> (\<lambda>j. x ::= (\<lambda>s. 1)) j | j \<in> {0,1}]"
        apply(rule)
        by(auto simp add:map_comprehension_def)
      show "\<Turnstile> {?Iv_p1} 
                    [[0 \<mapsto> x ::= (\<lambda>s. 1), 1 \<mapsto> x ::= (\<lambda>s. 1)]] 
               {?Iv_p1}"
      apply(simp only:eq2)
      apply(rule cons_prec)
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
          apply(rule cons_prec)
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
          apply(rule cons_post[where Q' = "conj ?Q (holds_forall_hyper {0,1} (lnot_hyper ?conds))"])
           apply (simp add: entail_conj_weaken)
          apply(rule while_nonfixed_lck_sync[where V = "?V" and Q = "?Q" and ?Q_inf="?Q"  and I="{0,1}" and ?bs = ?conds and ?Cs = ?bodies and Iv="?Iv"])
        proof -
          (*Step 4.1*)
          show "\<forall>n. \<forall>J\<in>(Pow {0,1} - {{}}). \<Turnstile> { conj (?Iv n) (conj (holds_forall_hyper J ?conds) (?V J))} [[i \<mapsto> ?bodies i | i \<in> J]] { ?Iv (Suc n) }"
          proof (intro allI ballI)
            fix n 
            fix J ::"nat set"
            assume "J\<in>(Pow {0,1} - {{}})"
            hence "J = {0} \<or> J = {1} \<or> J = {0,1}" by auto
            thus " \<Turnstile> { conj (?Iv n) (conj (holds_forall_hyper J ?conds) (?V J))} [[i \<mapsto> ?bodies i | i \<in> J]] { ?Iv (Suc n) }"
            proof (elim disjE)
              assume "J = {0}"
              (*Step 4.1.1*)
              show "\<Turnstile> { conj (?Iv n) (conj (holds_forall_hyper J ?conds) (?V J))} [[i \<mapsto> ?bodies i | i \<in> J]] { ?Iv (Suc n) }"
                apply(rule cons_prec[where ?P'="\<lambda>S. False"])
                 prefer 2
                 apply(rule false)
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
              show "\<Turnstile> { conj (?Iv n) (conj (holds_forall_hyper J ?conds) (?V J))} [[i \<mapsto> ?bodies i | i \<in> J]] { ?Iv (Suc n) }"
                apply(simp only:eq)
                apply(rule seq_extension[where ?R="conj (?Iv n) (conj (holds_forall_hyper J ?conds) (?V J))"])
                 apply(simp only:eq1)
                 apply(rule cons_prec[where ?P'="conj (conj (?Iv n) (conj (holds_forall_hyper J ?conds) (?V J))) (holds_forall_hyper {1} (lnot_hyper (\<lambda>j. \<lambda>s. prime (s c))))"])
                  prefer 2
                  apply(rule if_false_lck_simp)
                  apply(rule cons_post)
                   prefer 2
                   apply(rule skip_lockstep)
                  apply(intro entailsI)
                unfolding conj_def
                  apply meson
                 apply(intro entailsI)
                unfolding holds_forall_hyper_def holds_forall_hyper_def lnot_hyper_def
                 apply (smt (z3) \<open>J = {1}\<close> bot_nat_0.not_eq_extremum empty_iff insert_iff less_numeral_extra(1))
                apply(rule cons_prec)
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
              show "\<Turnstile> { conj (?Iv n) (conj (holds_forall_hyper J ?conds) (?V J))} [[i \<mapsto> ?bodies i | i \<in> J]] { ?Iv (Suc n) }"
                apply(simp only:eq)
                apply(rule seq_extension[where ?R="(?Iv n)"])
                 apply(simp only:eq1)
                 apply(rule cons_prec)
                prefer 2
                  apply(rule if_true_lck[where ?P="conj (?Iv n) (conj (holds_forall_hyper J ?conds) (?V J))"])
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
                 apply(rule seq_extension[where ?R = "(?Iv n)"])
                  apply(rule cons_prec)
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
                 apply(rule cons_prec)
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
                 apply(rule cons_prec)
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
          show "(progress_side_condition2_sync ?Iv {0,1} ?conds ?V)" 
          proof
            fix n::nat
            from bigger_prime obtain n' where "n \<le> n'" and "prime n'" 
              using order_less_imp_le by blast
            show "\<forall>i\<in>{0,1}. \<exists>n'\<ge>n. (entails (?Iv n') (disj (\<lambda>S. (holds_forall (lnot (?conds i)) (S i))) (disj_I ({J . J \<in> Pow {0,1} \<and> i \<in> J}) (\<lambda>J. conj (holds_forall_hyper J ?conds) (?V J)))))"
            unfolding disj_def disj_I_def
            proof(intro allI ballI impI entailsI conjI exI)
              from \<open>n \<le> n'\<close> show "n \<le> n'" by auto
            next
              fix i'::nat
              fix S'::"(nat \<Rightarrow> ((nat \<Rightarrow> nat) \<times> (nat \<Rightarrow> nat)) set)"
              assume "i' \<in> {0,1}" and "?Iv n' S'" 
              show "holds_forall (lnot (\<lambda>s. 0 < s i)) (S' i') \<or>
            (\<exists>ia\<in>{J \<in> Pow {0, 1}. i' \<in> J}.
                Logic.conj (holds_forall_hyper ia (\<lambda>j s. 0 < s i))
                 (if ia = {0, 1} then \<lambda>S. \<forall>\<sigma>1\<in>S 1. prime (snd \<sigma>1 c)
                  else if ia = {1} then \<lambda>S. \<forall>\<sigma>1\<in>S 1. \<not> prime (snd \<sigma>1 c) else (\<lambda>S. False))
                 S')"
                apply(subst disj_imp)
                apply(intro impI)
              proof -
              assume hfa:"\<not> holds_forall (lnot (\<lambda>s. 0 < s i)) (S' i')"
              from \<open>?Iv n' S'\<close> hfa have H1: "(holds_forall_hyper {0,1} (\<lambda>j s. 0 < s i)) S'" 
                unfolding holds_forall_hyper_def holds_forall_def lnot_def holds_forall_hyper_def
                using \<open>i' \<in> {0, 1}\<close>
                by (metis empty_iff insert_iff)
              from \<open>?Iv n' S'\<close>  \<open>prime n'\<close> have H2: "\<forall>\<sigma>1\<in>S' 1. prime (snd \<sigma>1 c)" by fastforce
              show "(\<exists>ia\<in>{J \<in> Pow {0, 1}. i' \<in> J}.
                Logic.conj (holds_forall_hyper ia (\<lambda>j s. 0 < s i))
                 (if ia = {0, 1} then \<lambda>S. \<forall>\<sigma>1\<in>S 1. prime (snd \<sigma>1 c)
                  else if ia = {1} then \<lambda>S. \<forall>\<sigma>1\<in>S 1. \<not> prime (snd \<sigma>1 c) else (\<lambda>S. False))
                 S')" 
              proof -
                have "i' \<in> {0,1} \<and> conj (holds_forall_hyper {0,1} (\<lambda>j s. 0 < s i))
                (if {0,1} = {0, 1} then \<lambda>S. \<forall>\<sigma>1\<in>S 1. prime (snd \<sigma>1 c) else if {0,1} = {1} then \<lambda>S. \<forall>\<sigma>1\<in>S 1. \<not> prime (snd \<sigma>1 c) else (\<lambda>S. False)) S'"
                  using H1 H2 \<open>i' \<in> {0,1}\<close>
                  by(auto simp add:conj_def)
                thus ?thesis
                  by blast
              qed
            qed
          qed
        qed
        next
          (*Step 4.3*)
          show "(progress_side_condition1_sync ?Iv {0,1} ?conds ?V)" 
          proof(intro allI entailsI)
            fix n S
            assume asm:"?Iv n S"
            from asm have "(\<forall>\<sigma>0\<in>S 0. \<not>(0 < snd \<sigma>0 i)) \<and> (\<forall>\<sigma>1\<in>S 1. \<not>(0 < snd \<sigma>1 i)) \<or> (\<forall>\<sigma>0\<in>S 0. (0 < snd \<sigma>0 i)) \<and> (\<forall>\<sigma>1\<in>S 1. (0 < snd \<sigma>1 i))"
              by metis
            thus "(disj (disj_I (Pow {0,1} - {{}}) (\<lambda>J. conj (holds_forall_hyper J ?conds) (?V J))) (holds_forall_hyper {0,1} (lnot_hyper ?conds))) S"
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
                show ?thesis unfolding disj_def disj_I_def conj_def holds_forall_hyper_def holds_forall_hyper_def
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
                show ?thesis unfolding disj_def disj_I_def conj_def holds_forall_hyper_def holds_forall_hyper_def
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
            apply(rule cons_prec[where ?P'="(\<lambda>S::nat hyper_set. (\<forall>\<sigma>0 \<in> (S 0). \<exists>\<sigma>1 \<in> (S 1). (snd \<sigma>0 x) = (snd \<sigma>1 x) \<and> (snd \<sigma>0 i) = (snd \<sigma>1 i)))"])
             apply(intro entailsI)
             apply fastforce
            apply(rule cons_prec)
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
        next
          show "{0, 1} \<noteq> {}" by auto
        qed
      qed
    qed
  qed
qed




end