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

function finite_map_fold :: "('a \<times> 'b \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> 'c \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> 'c" where
  "\<not> finite (dom m) \<Longrightarrow> finite_map_fold f c m = undefined"
| "finite (dom m) \<Longrightarrow> card (dom m) = 0 \<Longrightarrow> finite_map_fold f c m = c"
| "finite (dom m) \<Longrightarrow> card (dom m) \<noteq> 0 \<Longrightarrow> finite_map_fold f c m = (
    let x = SOME x. x \<in> dom m
    in f (x, the (m x)) (finite_map_fold f c (m(x := None))))"
  by atomize_elim auto
termination
  proof (relation "measure (card o dom o snd o snd)")
    show "wf (measure (card \<circ> dom o snd o snd))" by simp
  next
    fix f :: "'a \<times> 'b \<Rightarrow> 'c \<Rightarrow> 'c"
    fix m :: "'a \<rightharpoonup> 'b"
    fix c :: 'c 
    fix x
    assume "card (dom m) \<noteq> 0"
    then obtain y where "y \<in> dom m" by fastforce
    hence "\<exists>y. y \<in> dom m" by fastforce
    moreover assume "finite (dom m)"
    moreover assume "x = (SOME x. x \<in> dom m)"
    ultimately have "card (dom m - {x}) < card (dom m)" by (metis card_Diff1_less someI_ex)
    thus "((f, c, m(x := None)), f, c, m) \<in> measure (card \<circ> dom o snd o snd)" by simp
  qed

end