theory BasicComputation
imports Main
begin

typedecl code_label
typedecl function_name

axiomatization new_label :: "code_label set \<Rightarrow> code_label" where
  new_fresh [simp]: "finite ss \<Longrightarrow> new_label ss \<notin> ss"

datatype code_label\<^sub>2 = CL\<^sub>2 function_name code_label

axiomatization new_label\<^sub>2 :: "code_label\<^sub>2 set \<Rightarrow> code_label\<^sub>2" where
  new_fresh\<^sub>2 [simp]: "finite ss \<Longrightarrow> new_label\<^sub>2 ss \<notin> ss"

type_synonym "output" = "int list"

primrec repeat :: "'a \<Rightarrow> nat \<Rightarrow> 'a list" where
  "repeat a 0 = []"
| "repeat a (Suc n) = a # repeat a n"

definition boolify :: "int \<Rightarrow> bool" where
  "boolify i = (i \<noteq> 0)"

definition unboolify :: "bool \<Rightarrow> int" where
  "unboolify b = (if b then 1 else 0)"

lemma [simp]: "length (repeat v n) = n"
  by (induction n) simp_all

lemma [simp]: "unboolify True = 1"
  by (simp add: unboolify_def)

lemma [simp]: "unboolify False = 0"
  by (simp add: unboolify_def)

lemma [simp]: "boolify (unboolify b) = b"
  by (cases b) (simp_all add: boolify_def)

end