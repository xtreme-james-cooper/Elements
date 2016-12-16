theory BranchingAssemblyLanguage
imports CPU
begin

datatype branching_assembly =
  ABAssm int
| CBAssm "register set" computation
| IBAssm "comparison set" "branching_assembly list" "branching_assembly list"
| JBAssm code_label

type_synonym branching_assembly_program = "code_label \<rightharpoonup> branching_assembly list"

type_synonym branching_assembly_state = "memory \<times> int option \<times> int \<times> branching_assembly list" 
  (* \<mu>, a, d, pc *)

fun eval_branching_assembly :: "branching_assembly_program \<Rightarrow> branching_assembly_state \<Rightarrow> 
    branching_assembly_state option" where
  "eval_branching_assembly \<Pi> (\<mu>, a, d, []) = None"
| "eval_branching_assembly \<Pi> (\<mu>, a, d, ABAssm x # \<pi>) = Some (\<mu>, Some x, d, \<pi>)"
| "eval_branching_assembly \<Pi> (\<mu>, Some a, d, CBAssm dst cmp # \<pi>) = (
    let n = compute cmp (\<mu> a) a d
    in Some (
      if M \<in> dst then \<mu>(a := n) else \<mu>, 
      Some (if A \<in> dst then n else a), 
      if D \<in> dst then n else d, 
      \<pi>))"
| "eval_branching_assembly \<Pi> (\<mu>, None, d, CBAssm dst cmp # \<pi>) = None"
| "eval_branching_assembly \<Pi> (\<mu>, a, d, IBAssm cmp \<pi>\<^sub>t \<pi>\<^sub>f # \<pi>) = 
    Some (\<mu>, a, d, (if should_jump d cmp then \<pi>\<^sub>t else \<pi>\<^sub>f) @ \<pi>)"
| "eval_branching_assembly \<Pi> (\<mu>, a, d, JBAssm s # \<pi>) = (
    case \<Pi> s of 
      Some \<pi>' \<Rightarrow> Some (\<mu>, None, d, \<pi>')
    | None \<Rightarrow> None)"

end