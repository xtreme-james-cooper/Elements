theory MachineLanguage
imports CPU
begin

datatype machine_instruction =
  AInstr int
| CInstr "register set" computation "comparison set"
| PInstr

type_synonym machine_program = "machine_instruction list"

type_synonym machine_state = "memory \<times> int \<times> int \<times> nat \<times> output" (* \<mu>, a, d, pc, \<omega> *)

fun eval_instruction :: "machine_instruction \<Rightarrow> machine_state \<Rightarrow> machine_state" where
  "eval_instruction (AInstr x) (\<mu>, a, d, pc, \<omega>) = (\<mu>, x, d, Suc pc, \<omega>)"
| "eval_instruction (CInstr dst cmp jmp) (\<mu>, a, d, pc, \<omega>) = (
    let n = compute cmp (\<mu> a) a d
    in (if M \<in> dst then \<mu>(a := n) else \<mu>, 
        if A \<in> dst then n else a, 
        if D \<in> dst then n else d, 
        if should_jump n jmp then nat a else Suc pc,
        \<omega>))"
| "eval_instruction PInstr (\<mu>, a, d, pc, \<omega>) = (\<mu>, a, d, Suc pc, d # \<omega>)"

fun eval_machine :: "machine_program \<Rightarrow> machine_state \<Rightarrow> machine_state option" where
  "eval_machine \<Pi> (\<mu>, a, d, pc, \<omega>) = (
    if pc < length \<Pi> 
    then Some (eval_instruction (\<Pi> ! pc) (\<mu>, a, d, pc, \<omega>)) 
    else None)"

end