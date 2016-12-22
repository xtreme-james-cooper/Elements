theory BasicComputation
imports Main
begin

typedecl code_label

axiomatization new_label :: "code_label set \<Rightarrow> code_label" where
  new_fresh [simp]: "finite ss \<Longrightarrow> new_label ss \<notin> ss"

type_synonym "output" = "int list"

definition boolify :: "int \<Rightarrow> bool" where
  "boolify i = (i \<noteq> 0)"

definition unboolify :: "bool \<Rightarrow> int" where
  "unboolify b = (if b then 1 else 0)"

lemma [simp]: "unboolify True = 1"
  by (simp add: unboolify_def)

lemma [simp]: "unboolify False = 0"
  by (simp add: unboolify_def)

lemma [simp]: "boolify (unboolify b) = b"
  by (cases b) (simp_all add: boolify_def)

end