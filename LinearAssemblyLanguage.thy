theory LinearAssemblyLanguage
imports AssemblyLanguage FiniteMap Iterate
begin

type_synonym l_assembly_program = "code_label \<leadsto> assembly list"

fun eval_l_assembly :: "l_assembly_program \<Rightarrow> assembly_state \<Rightarrow> assembly_state option" where
  "eval_l_assembly \<Pi> (\<mu>, a, d, []) = None"
| "eval_l_assembly \<Pi> (\<mu>, a, d, AAssm x # \<pi>) = Some (\<mu>, Some x, d, \<pi>)"
| "eval_l_assembly \<Pi> (\<mu>, Some a, d, CAssm dst cmp # \<pi>) = (
    let n = compute cmp (\<mu> a) a d
    in Some (
      if M \<in> dst then \<mu>(a := n) else \<mu>, 
      Some (if A \<in> dst then n else a), 
      if D \<in> dst then n else d, 
      \<pi>))"
| "eval_l_assembly \<Pi> (\<mu>, None, d, CAssm dst cmp # \<pi>) = None"
| "eval_l_assembly \<Pi> (\<mu>, a, d, JAssm jmp s # \<pi>) = (
    if should_jump d jmp
    then case lookup \<Pi> s of 
        Some \<pi>' \<Rightarrow> Some (\<mu>, None, d, \<pi>')
      | None \<Rightarrow> None
    else Some (\<mu>, None, d, \<pi>))"

(* linearization correct *)

lemma [simp]: "finite (dom \<Pi>) \<Longrightarrow> eval_assembly \<Pi> \<Sigma> = Some \<Sigma>' \<Longrightarrow> 
    eval_l_assembly (linearize \<Pi>) \<Sigma> = Some \<Sigma>'"
  proof (induction \<Pi> \<Sigma> rule: eval_assembly.induct)
  case 1
    from 1(2) show ?case by simp
  next case 2
    thus ?case by simp
  next case 3
    thus ?case by simp
  next case 4
    from 4(2) show ?case by simp
  next case 5
    thus ?case by auto
  qed 

theorem linearization_correct [simp]: "iterate (eval_assembly \<Pi>) \<Sigma> \<Sigma>' \<Longrightarrow> finite (dom \<Pi>) \<Longrightarrow> 
    iterate (eval_l_assembly (linearize \<Pi>)) \<Sigma> \<Sigma>'"
  by (induction "eval_assembly \<Pi>" \<Sigma> \<Sigma>' rule: iterate.induct) simp_all

end