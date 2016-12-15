theory AssemblyLanguage
imports FiniteMap BasicComputation
begin

typedecl symbol

datatype assembly =
  AAssm int
| CAssm "register set" computation
| JAssm "comparison set" symbol

type_synonym program = "symbol \<leadsto> assembly list"

type_synonym assembly_state = "memory \<times> int option \<times> int \<times> assembly list" (* \<mu>, a, d, pc *)

fun eval_assembly :: "program \<Rightarrow> assembly_state \<Rightarrow> assembly_state option" where
  "eval_assembly \<Pi> (\<mu>, a, d, []) = None"
| "eval_assembly \<Pi> (\<mu>, a, d, AAssm x # \<pi>) = Some (\<mu>, Some x, d, \<pi>)"
| "eval_assembly \<Pi> (\<mu>, Some a, d, CAssm dst cmp # \<pi>) = (
    let n = compute cmp (\<mu> a) a d
    in Some (
      if M \<in> dst then \<mu>(a := n) else \<mu>, 
      Some (if A \<in> dst then n else a), 
      if D \<in> dst then n else d, 
      \<pi>))"
| "eval_assembly \<Pi> (\<mu>, None, d, CAssm dst cmp # \<pi>) = None"
| "eval_assembly \<Pi> (\<mu>, a, d, JAssm jmp s # \<pi>) = (
    if should_jump d jmp
    then case lookup \<Pi> s of 
        Some \<pi>' \<Rightarrow> Some (\<mu>, None, d, \<pi>')
      | None \<Rightarrow> None
    else Some (\<mu>, None, d, \<pi>))"

end