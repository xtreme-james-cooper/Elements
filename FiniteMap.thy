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

definition linearize :: "('a \<rightharpoonup> 'b) \<Rightarrow> 'a \<leadsto> 'b" where
  "linearize f = finite_map_fold (op #) [] f"

lemma [simp]: "finite (dom f) \<Longrightarrow> lookup (finite_map_fold (op #) [] f) x = f x"
  proof (induction "(op #)::('a \<times> 'b) \<Rightarrow> 'a \<leadsto> 'b \<Rightarrow> 'a \<leadsto> 'b" "[]::'a \<leadsto> 'b" f 
         rule: finite_map_fold.induct)
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
          by (metis (mono_tags, lifting) domIff fun_upd_triv finite_map_fold.simps(3) 
              not_Cons_self2 option.collapse someI_ex)
        with 3 True show ?thesis by (simp add: Let_def)
      next case False
        from 3 have "lookup (finite_map_fold (op #) [] (f(?x := None))) x = (f(?x := None)) x" 
          by fastforce
        with 3 False show ?thesis by (simp add: Let_def)
      qed
  qed

lemma [simp]: "finite (dom f) \<Longrightarrow> lookup (linearize f) x = f x"
  by (simp add: linearize_def)

lemma [simp]: "finite (dom f) \<Longrightarrow> domain_distinct (finite_map_fold (op #) [] f)"
  proof (induction "(op #)::('a \<times> 'b) \<Rightarrow> 'a \<leadsto> 'b \<Rightarrow> 'a \<leadsto> 'b" "[]::'a \<leadsto> 'b" f 
         rule: finite_map_fold.induct)
  case 1
    thus ?case by simp
  next case 2
    thus ?case by simp
  next case (3 f)
    let ?x = "SOME x. x \<in> dom f"
    from 3 have "domain_distinct (finite_map_fold (op #) [] (f(?x := None)))" by fastforce
    with 3 show ?case by (auto simp add: Let_def)
  qed

lemma [simp]: "finite (dom f) \<Longrightarrow> domain_distinct (linearize f)"
  by (simp add: linearize_def)

end