theory AssemblyLanguage
imports "../Machine/CPU"
begin

datatype assembly =
  AAssm int
| CAssm "register set" computation
| JAssm "comparison set" code_label
| PAssm

type_synonym assembly_program = "code_label \<rightharpoonup> assembly list \<times> code_label"

type_synonym assembly_state = "memory \<times> int option \<times> int \<times> assembly list \<times> code_label \<times> output" 
  (* \<mu>, a, d, \<pi>, s, \<omega> *)

fun eval_assembly :: "assembly_program \<Rightarrow> assembly_state \<Rightarrow> assembly_state option" where
  "eval_assembly \<Pi> (\<mu>, a, d, [], s, \<omega>) = (case \<Pi> s of 
      Some (\<pi>', s') \<Rightarrow> Some (\<mu>, None, d, \<pi>', s', \<omega>)
    | None \<Rightarrow> None)"
| "eval_assembly \<Pi> (\<mu>, a, d, AAssm x # \<pi>, s, \<omega>) = Some (\<mu>, Some x, d, \<pi>, s, \<omega>)"
| "eval_assembly \<Pi> (\<mu>, Some a, d, CAssm dst cmp # \<pi>, s, \<omega>) = (
    let n = compute cmp (\<mu> a) a d
    in Some (
      if M \<in> dst then \<mu>(a := n) else \<mu>, 
      Some (if A \<in> dst then n else a), 
      if D \<in> dst then n else d, 
      \<pi>, s, \<omega>))"
| "eval_assembly \<Pi> (\<mu>, None, d, CAssm dst cmp # \<pi>, s, \<omega>) = None"
| "eval_assembly \<Pi> (\<mu>, a, d, JAssm jmp s # \<pi>, s', \<omega>) = (
    if should_jump d jmp
    then case \<Pi> s of 
        Some (\<pi>', s'') \<Rightarrow> Some (\<mu>, None, d, \<pi>', s'', \<omega>)
      | None \<Rightarrow> None
    else Some (\<mu>, None, d, \<pi>, s', \<omega>))"
| "eval_assembly \<Pi> (\<mu>, a, d, PAssm # \<pi>, s, \<omega>) = Some (\<mu>, a, d, \<pi>, s, d # \<omega>)"

fun assembly_output :: "assembly_state \<Rightarrow> output" where
  "assembly_output (\<mu>, a, d, \<pi>, s, \<omega>) = \<omega>"

end