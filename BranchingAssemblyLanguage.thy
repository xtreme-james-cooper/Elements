theory BranchingAssemblyLanguage
imports CPU
begin

datatype b_assembly =
  ABAssm int
| CBAssm "register set" computation
| IBAssm "comparison set" "b_assembly list" "b_assembly list"
| JBAssm code_label
| PBAssm

type_synonym b_assembly_program = "code_label \<rightharpoonup> b_assembly list"

type_synonym b_assembly_state = "memory \<times> int option \<times> int \<times> b_assembly list \<times> output" 
  (* \<mu>, a, d, \<pi>, \<omega> *)

fun eval_b_assembly :: "b_assembly_program \<Rightarrow> b_assembly_state \<Rightarrow> b_assembly_state option" where
  "eval_b_assembly \<Pi> (\<mu>, a, d, [], \<omega>) = None"
| "eval_b_assembly \<Pi> (\<mu>, a, d, ABAssm x # \<pi>, \<omega>) = Some (\<mu>, Some x, d, \<pi>, \<omega>)"
| "eval_b_assembly \<Pi> (\<mu>, Some a, d, CBAssm dst cmp # \<pi>, \<omega>) = (
    let n = compute cmp (\<mu> a) a d
    in Some (
      if M \<in> dst then \<mu>(a := n) else \<mu>, 
      Some (if A \<in> dst then n else a), 
      if D \<in> dst then n else d, 
      \<pi>, 
      \<omega>))"
| "eval_b_assembly \<Pi> (\<mu>, None, d, CBAssm dst cmp # \<pi>, \<omega>) = None"
| "eval_b_assembly \<Pi> (\<mu>, a, d, IBAssm cmp \<pi>\<^sub>t \<pi>\<^sub>f # \<pi>, \<omega>) = 
    Some (\<mu>, a, d, (if should_jump d cmp then \<pi>\<^sub>t else \<pi>\<^sub>f) @ \<pi>, \<omega>)"
| "eval_b_assembly \<Pi> (\<mu>, a, d, JBAssm s # \<pi>, \<omega>) = (
    case \<Pi> s of 
      Some \<pi>' \<Rightarrow> Some (\<mu>, None, d, \<pi>', \<omega>)
    | None \<Rightarrow> None)"
| "eval_b_assembly \<Pi> (\<mu>, a, d, PBAssm # \<pi>, \<omega>) = Some (\<mu>, a, d, \<pi>, d # \<omega>)"

fun b_assembly_output :: "b_assembly_state \<Rightarrow> output" where
  "b_assembly_output (\<mu>, a, d, \<pi>, \<omega>) = \<omega>"

end