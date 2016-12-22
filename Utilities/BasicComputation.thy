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

fun list_update :: "'a list \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a list" where
  "list_update as a' 0 = a' # as"
| "list_update [] a' (Suc n) = undefined"
| "list_update (a # as) a' (Suc n) = a # list_update as a' n"

lemma [simp]: "unboolify True = 1"
  by (simp add: unboolify_def)

lemma [simp]: "unboolify False = 0"
  by (simp add: unboolify_def)

lemma [simp]: "boolify (unboolify b) = b"
  by (cases b) (simp_all add: boolify_def)

end