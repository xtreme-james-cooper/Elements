theory LinearAssemblyLanguage
imports "../Assembly/AssemblyLanguage" "../Utilities/FiniteMap"
begin

type_synonym l_assembly_state = "memory \<times> int option \<times> int \<times> assembly list \<times> output" 
  (* \<mu>, a, d, \<pi>, \<omega> *)

type_synonym l_assembly_program = "code_label\<^sub>2 \<leadsto> assembly list"

fun eval_l_assembly :: "l_assembly_program \<Rightarrow> l_assembly_state \<Rightarrow> l_assembly_state option" where
  "eval_l_assembly \<Pi> (\<mu>, a, d, [], \<omega>) = None"
| "eval_l_assembly \<Pi> (\<mu>, a, d, AAssm x # \<pi>, \<omega>) = Some (\<mu>, Some x, d, \<pi>, \<omega>)"
| "eval_l_assembly \<Pi> (\<mu>, Some a, d, CAssm dst cmp # \<pi>, \<omega>) = (
    let n = compute cmp (\<mu> (nat a)) a d
    in Some (
      if M \<in> dst then \<mu>(nat a := n) else \<mu>, 
      Some (if A \<in> dst then n else a), 
      if D \<in> dst then n else d, 
      \<pi>, \<omega>))"
| "eval_l_assembly \<Pi> (\<mu>, None, d, CAssm dst cmp # \<pi>, \<omega>) = None"
| "eval_l_assembly \<Pi> (\<mu>, a, d, JAssm jmp s # \<pi>, \<omega>) = (
    if compare d jmp
    then case lookup \<Pi> s of 
        Some \<pi>' \<Rightarrow> Some (\<mu>, None, d, \<pi>', \<omega>)
      | None \<Rightarrow> None
    else Some (\<mu>, None, d, \<pi>, \<omega>))"
| "eval_l_assembly \<Pi> (\<mu>, a, d, Print # \<pi>, \<omega>) = Some (\<mu>, a, d, \<pi>, d # \<omega>)"

fun l_assembly_output :: "l_assembly_state \<Rightarrow> output" where
  "l_assembly_output (\<mu>, a, d, \<pi>, \<omega>) = \<omega>"

end