theory LinearAssemblyLanguage
imports AssemblyLanguage FiniteMap Iterate
begin

type_synonym l_assembly_state = "memory \<times> int option \<times> int \<times> assembly list \<times> output" 
  (* \<mu>, a, d, \<pi>, \<omega> *)

type_synonym l_assembly_program = "code_label \<leadsto> assembly list"

fun eval_l_assembly :: "l_assembly_program \<Rightarrow> l_assembly_state \<Rightarrow> l_assembly_state option" where
  "eval_l_assembly \<Pi> (\<mu>, a, d, [], \<omega>) = None"
| "eval_l_assembly \<Pi> (\<mu>, a, d, AAssm x # \<pi>, \<omega>) = Some (\<mu>, Some x, d, \<pi>, \<omega>)"
| "eval_l_assembly \<Pi> (\<mu>, Some a, d, CAssm dst cmp # \<pi>, \<omega>) = (
    let n = compute cmp (\<mu> a) a d
    in Some (
      if M \<in> dst then \<mu>(a := n) else \<mu>, 
      Some (if A \<in> dst then n else a), 
      if D \<in> dst then n else d, 
      \<pi>, \<omega>))"
| "eval_l_assembly \<Pi> (\<mu>, None, d, CAssm dst cmp # \<pi>, \<omega>) = None"
| "eval_l_assembly \<Pi> (\<mu>, a, d, JAssm jmp s # \<pi>, \<omega>) = (
    if should_jump d jmp
    then case lookup \<Pi> s of 
        Some \<pi>' \<Rightarrow> Some (\<mu>, None, d, \<pi>', \<omega>)
      | None \<Rightarrow> None
    else Some (\<mu>, None, d, \<pi>, \<omega>))"
| "eval_l_assembly \<Pi> (\<mu>, a, d, Print # \<pi>, \<omega>) = Some (\<mu>, a, d, \<pi>, d # \<omega>)"

(* linearization correct *)

lemma [simp]: "finite (dom \<Pi>) \<Longrightarrow> eval_assembly \<Pi> \<Sigma> = Some \<Sigma>' \<Longrightarrow> 
    eval_l_assembly (linearize \<Pi>) \<Sigma> = Some \<Sigma>'"
  by (induction \<Pi> \<Sigma> rule: eval_assembly.induct) auto

theorem linearization_correct [simp]: "iterate (eval_assembly \<Pi>) \<Sigma> \<Sigma>' \<Longrightarrow> finite (dom \<Pi>) \<Longrightarrow> 
    iterate (eval_l_assembly (linearize \<Pi>)) \<Sigma> \<Sigma>'"
  by (induction "eval_assembly \<Pi>" \<Sigma> \<Sigma>' rule: iterate.induct) simp_all

end