theory FiniteMap
imports Main
begin

type_synonym ('a, 'b) finite_map = "('a \<times> 'b) list" (infixr "\<leadsto>" 50)

fun lookup :: "'a \<leadsto> 'b \<Rightarrow> 'a \<rightharpoonup> 'b" where
  "lookup [] k = None"
| "lookup ((a, b) # ab) k = (if a = k then Some b else lookup ab k)"

fun domain_distinct :: "'a \<leadsto> 'b \<Rightarrow> bool" where
  "domain_distinct [] = True"
| "domain_distinct ((a, b) # ab) = (domain_distinct ab \<and> a \<notin> dom (lookup ab))"

end