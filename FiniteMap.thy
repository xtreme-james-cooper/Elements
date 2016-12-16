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

function linearize :: "('a \<rightharpoonup> 'b) \<Rightarrow> 'a \<leadsto> 'b" where
  "\<not> finite (dom f) \<Longrightarrow> linearize f = undefined"
| "finite (dom f) \<Longrightarrow> card (dom f) = 0 \<Longrightarrow> linearize f = []"
| "finite (dom f) \<Longrightarrow> card (dom f) \<noteq> 0 \<Longrightarrow> linearize f = (
    let x = SOME x. x \<in> dom f
    in (x, the (f x)) # linearize (f(x := None)))"
  by atomize_elim auto
termination
  proof (relation "measure (card o dom)")
    show "wf (measure (card \<circ> dom))" by simp
  next
    fix f :: "'a \<rightharpoonup> 'b"
    fix x
    assume "card (dom f) \<noteq> 0"
    then obtain y where "y \<in> dom f" by fastforce
    hence "\<exists>y. y \<in> dom f" by fastforce
    moreover assume "finite (dom f)"
    moreover assume "x = (SOME x. x \<in> dom f)"
    ultimately have "card (dom f - {x}) < card (dom f)" by (metis card_Diff1_less someI_ex)
    thus "(f(x := None), f) \<in> measure (card \<circ> dom)" by simp
  qed

lemma [simp]: "finite (dom f) \<Longrightarrow> lookup (linearize f) x = f x"
  proof (induction f rule: linearize.induct)
  case 1
    thus ?case by simp
  next case 2
    thus ?case by simp
  next case (3 f)
    let ?x = "SOME x. x \<in> dom f"
    show ?case
      proof (cases "x = ?x")
      case True
        from 3 have "Some (the (f ?x)) = f ?x" 
          by (metis (mono_tags, lifting) domIff fun_upd_triv linearize.simps(3) 
              not_Cons_self2 option.collapse someI_ex)
        with 3 True show ?thesis by (simp add: Let_def)
      next case False
        from 3 have "lookup (linearize (f(?x := None))) x = (f(?x := None)) x" by fastforce
        with 3 False show ?thesis by (simp add: Let_def)
      qed
  qed

lemma [simp]: "finite (dom f) \<Longrightarrow> domain_distinct (linearize f)"
  proof (induction f rule: linearize.induct)
  case 1
    thus ?case by simp
  next case 2
    thus ?case by simp
  next case (3 f)
    let ?x = "SOME x. x \<in> dom f"
    from 3 have "domain_distinct (linearize (f(?x := None)))" by fastforce
    with 3 show ?case by (auto simp add: Let_def)
  qed

end