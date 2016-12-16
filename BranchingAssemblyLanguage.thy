theory BranchingAssemblyLanguage
imports CPU
begin

datatype b_assembly =
  ABAssm int
| CBAssm "register set" computation
| IBAssm "comparison set" "b_assembly list" "b_assembly list"
| JBAssm code_label

type_synonym b_assembly_program = "code_label \<rightharpoonup> b_assembly list"

type_synonym b_assembly_state = "memory \<times> int option \<times> int \<times> b_assembly list" 
  (* \<mu>, a, d, \<pi> *)

fun eval_b_assembly :: "b_assembly_program \<Rightarrow> b_assembly_state \<Rightarrow> b_assembly_state option" where
  "eval_b_assembly \<Pi> (\<mu>, a, d, []) = None"
| "eval_b_assembly \<Pi> (\<mu>, a, d, ABAssm x # \<pi>) = Some (\<mu>, Some x, d, \<pi>)"
| "eval_b_assembly \<Pi> (\<mu>, Some a, d, CBAssm dst cmp # \<pi>) = (
    let n = compute cmp (\<mu> a) a d
    in Some (
      if M \<in> dst then \<mu>(a := n) else \<mu>, 
      Some (if A \<in> dst then n else a), 
      if D \<in> dst then n else d, 
      \<pi>))"
| "eval_b_assembly \<Pi> (\<mu>, None, d, CBAssm dst cmp # \<pi>) = None"
| "eval_b_assembly \<Pi> (\<mu>, a, d, IBAssm cmp \<pi>\<^sub>t \<pi>\<^sub>f # \<pi>) = 
    Some (\<mu>, a, d, (if should_jump d cmp then \<pi>\<^sub>t else \<pi>\<^sub>f) @ \<pi>)"
| "eval_b_assembly \<Pi> (\<mu>, a, d, JBAssm s # \<pi>) = (
    case \<Pi> s of 
      Some \<pi>' \<Rightarrow> Some (\<mu>, None, d, \<pi>')
    | None \<Rightarrow> None)"

end