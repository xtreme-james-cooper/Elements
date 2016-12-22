theory BranchingAssemblyLanguage
imports "../Machine/CPU"
begin

datatype b_assembly =
  ABAssm int
| CBAssm "register set" computation
| IBAssm "comparison set" "b_assembly list" "b_assembly list"
| PBAssm

type_synonym b_assembly_program = "code_label \<rightharpoonup> b_assembly list \<times> code_label"

type_synonym b_assembly_state = "memory \<times> int option \<times> int \<times> b_assembly list \<times> code_label \<times> output" 
  (* \<mu>, a, d, \<pi>, s, \<omega> *)

fun eval_b_assembly :: "b_assembly_program \<Rightarrow> b_assembly_state \<Rightarrow> b_assembly_state option" where
  "eval_b_assembly \<Pi> (\<mu>, a, d, [], s, \<omega>) = (
    case \<Pi> s of 
      Some (\<pi>', s') \<Rightarrow> Some (\<mu>, None, d, \<pi>', s', \<omega>)
    | None \<Rightarrow> None)"
| "eval_b_assembly \<Pi> (\<mu>, a, d, ABAssm x # \<pi>, s, \<omega>) = Some (\<mu>, Some x, d, \<pi>, s, \<omega>)"
| "eval_b_assembly \<Pi> (\<mu>, Some a, d, CBAssm dst cmp # \<pi>, s, \<omega>) = (
    let n = compute cmp (\<mu> (nat a)) a d
    in Some (
      if M \<in> dst then \<mu>(nat a := n) else \<mu>, 
      Some (if A \<in> dst then n else a), 
      if D \<in> dst then n else d, 
      \<pi>, s, \<omega>))"
| "eval_b_assembly \<Pi> (\<mu>, None, d, CBAssm dst cmp # \<pi>, s, \<omega>) = None"
| "eval_b_assembly \<Pi> (\<mu>, a, d, IBAssm jmp \<pi>\<^sub>t \<pi>\<^sub>f # \<pi>, s, \<omega>) = 
    Some (\<mu>, None, d, (if should_jump d jmp then \<pi>\<^sub>t else \<pi>\<^sub>f) @ \<pi>, s, \<omega>)"
| "eval_b_assembly \<Pi> (\<mu>, a, d, PBAssm # \<pi>, s, \<omega>) = Some (\<mu>, a, d, \<pi>, s, d # \<omega>)"

fun b_assembly_output :: "b_assembly_state \<Rightarrow> output" where
  "b_assembly_output (\<mu>, a, d, \<pi>, s, \<omega>) = \<omega>"

end