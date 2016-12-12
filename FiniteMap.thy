theory FiniteMap
imports Main
begin

type_synonym ('a, 'b) finite_map = "('a \<times> 'b) list" (infixr "\<leadsto>" 50)

fun lookup :: "'a \<leadsto> 'b \<Rightarrow> 'a \<rightharpoonup> 'b" where
  "lookup [] k = None"
| "lookup ((a, b) # ab) k = (if a = k then Some b else lookup ab k)"

end