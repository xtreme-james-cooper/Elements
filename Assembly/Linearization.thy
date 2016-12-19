theory Linearization
imports "../LinearAssembly/LinearAssemblyLanguage" "../Utilities/Iterate"
begin

fun state_convert :: "assembly_state \<Rightarrow> l_assembly_state" where
  "state_convert (\<mu>, a, d, \<pi>, s, \<omega>) = (\<mu>, a, d, \<pi> @ [JAssm {EQ, GT, LT} s], \<omega>)"

fun linearize_step :: "code_label \<times> assembly list \<times> code_label \<Rightarrow> l_assembly_program \<Rightarrow> 
    l_assembly_program" where
  "linearize_step (s, \<pi>, s') \<Pi> = (s, \<pi> @ [JAssm {EQ, GT, LT} s']) # \<Pi>"

definition linearize :: "assembly_program \<Rightarrow> l_assembly_program" where
  "linearize \<Pi> = finite_map_fold linearize_step [] \<Pi>"

(* linearization correct *)

lemma [simp]: "l_assembly_output (state_convert \<Sigma>\<^sub>A) = assembly_output \<Sigma>\<^sub>A"
  by (induction \<Sigma>\<^sub>A rule: state_convert.induct) simp

lemma [simp]: "finite (dom \<Pi>) \<Longrightarrow> \<Pi> x = None \<Longrightarrow> 
    lookup (finite_map_fold linearize_step [] \<Pi>) x = None"
  proof (induction linearize_step "[]::code_label \<leadsto> assembly list" \<Pi> rule: finite_map_fold.induct)
  case 1
    thus ?case by metis
  next case 2
    thus ?case by simp
  next case (3 \<Pi>)
    let ?x = "SOME x. x \<in> dom \<Pi>"
    let ?ih = "finite_map_fold linearize_step [] (\<Pi>(?x := None))"
    from 3 have "?x \<in> dom \<Pi>" by (smt Collect_empty_eq card_0_eq dom_def mem_Collect_eq someI_ex)
    with 3 have "x \<noteq> ?x" by blast
    with 3 show ?case by (cases "the (\<Pi> ?x)") (simp add: Let_def)
  qed

lemma [simp]: "finite (dom \<Pi>) \<Longrightarrow> \<Pi> x = Some (\<pi>, s) \<Longrightarrow> 
    lookup (finite_map_fold linearize_step [] \<Pi>) x = Some (\<pi> @ [JAssm {EQ, GT, LT} s])"
  proof (induction linearize_step "[]::code_label \<leadsto> assembly list" \<Pi> rule: finite_map_fold.induct)
  case 1
    thus ?case by metis
  next case 2
    thus ?case by (metis card_0_eq dom_eq_empty_conv option.distinct(1))
  next case (3 \<Pi>)
    let ?x = "SOME x. x \<in> dom \<Pi>"
    let ?ih = "finite_map_fold linearize_step [] (\<Pi>(?x := None))"
    show ?case
      proof (cases "x = ?x")
      case True
        with 3 have "\<Pi> ?x = Some (\<pi>, s)" by blast
        with True have "lookup (linearize_step (?x, the (\<Pi> ?x)) ?ih) x = 
          Some (\<pi> @ [JAssm {EQ, GT, LT} s])" by (cases "the (\<Pi> ?x)") simp
        with 3 show ?thesis by (simp add: Let_def)
      next case False
        with 3 show ?thesis by (cases "the (\<Pi> ?x)") (simp add: Let_def)
      qed
  qed

lemma [simp]: "finite (dom \<Pi>) \<Longrightarrow> \<Pi> x = Some (\<pi>, s) \<Longrightarrow> 
    lookup (linearize \<Pi>) x = Some (\<pi> @ [JAssm {EQ, GT, LT} s])"
  by (simp add: linearize_def)

lemma [simp]: "finite (dom \<Pi>) \<Longrightarrow> domain_distinct (finite_map_fold linearize_step [] \<Pi>)"
  proof (induction linearize_step "[]::code_label \<leadsto> assembly list" \<Pi> rule: finite_map_fold.induct)
  case 1
    thus ?case by metis
  next case 2
    thus ?case by simp
  next case (3 \<Pi>)
    let ?x = "SOME x. x \<in> dom \<Pi>"
    let ?ih = "finite_map_fold linearize_step [] (\<Pi>(?x := None))"
    show ?case
      proof (cases "the (\<Pi> ?x)")
      case (Pair \<pi> s)
        from 3 have "lookup ?ih ?x = None" by simp
        hence "?x \<notin> dom (lookup ?ih)" by auto
        with 3 Pair show ?thesis by (simp add: Let_def)
      qed
  qed

lemma [simp]: "finite (dom \<Pi>) \<Longrightarrow> domain_distinct (linearize \<Pi>)"
  by (simp add: linearize_def)

lemma [simp]: "finite (dom \<Pi>) \<Longrightarrow> eval_assembly \<Pi> \<Sigma> = Some \<Sigma>' \<Longrightarrow> 
    eval_l_assembly (linearize \<Pi>) (state_convert \<Sigma>) = Some (state_convert \<Sigma>')"
  proof (induction \<Pi> \<Sigma> rule: eval_assembly.induct)
  case (1 \<Pi> \<mu> a d s \<omega>)
    thus ?case by (cases "\<Pi> s") (auto split: prod.splits)
  next case 2
    thus ?case by auto
  next case 3
    thus ?case by (auto simp add: Let_def)
  next case 4
    thus ?case by simp
  next case (5 \<Pi> \<mu> a d jmp s \<pi> s' \<omega>)
    thus ?case by (cases "\<Pi> s") auto
  next case 6
    thus ?case by auto
  qed

theorem linearization_correct [simp]: "iterate (eval_assembly \<Pi>) \<Sigma> \<Sigma>' \<Longrightarrow> finite (dom \<Pi>) \<Longrightarrow> 
    iterate (eval_l_assembly (linearize \<Pi>)) (state_convert \<Sigma>) (state_convert \<Sigma>')"
  by (induction "eval_assembly \<Pi>" \<Sigma> \<Sigma>' rule: iterate.induct) simp_all

end