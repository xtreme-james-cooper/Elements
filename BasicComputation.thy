theory BasicComputation
imports Main
begin

typedecl code_label

axiomatization new_label :: "code_label set \<Rightarrow> code_label" where
  new_fresh [simp]: "finite ss \<Longrightarrow> new_label ss \<notin> ss"

type_synonym "output" = "int list"

definition boolify :: "int \<Rightarrow> bool" where
  "boolify i = (i = 0)"

definition unboolify :: "bool \<Rightarrow> int" where
  "unboolify b = (if b then 1 else 0)"

lemma [simp]: "unboolify (boolify i2 \<and> boolify i1) = unboolify (boolify i1 \<and> boolify i2)"
  by (simp add: boolify_def unboolify_def)

lemma [simp]: "unboolify (boolify i2 \<or> boolify i1) = unboolify (boolify i1 \<or> boolify i2)"
  by (simp add: boolify_def unboolify_def)

end