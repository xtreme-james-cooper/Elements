theory MachineLanguage
imports BasicComputation
begin

datatype machine_instruction =
  AInstr int
| CInstr "register set" computation "comparison set"

type_synonym machine_state = "memory \<times> int \<times> int \<times> nat" (* \<mu>, a, d, pc *)

fun eval_instruction :: "machine_instruction \<Rightarrow> machine_state \<Rightarrow> machine_state" where
  "eval_instruction (AInstr x) (\<mu>, a, d, pc) = (\<mu>, x, d, Suc pc)"
| "eval_instruction (CInstr dst cmp jmp) (\<mu>, a, d, pc) = (
    let n = compute cmp (\<mu> a) a d
    in (if M \<in> dst then \<mu>(a := n) else \<mu>, 
        if A \<in> dst then n else a, 
        if D \<in> dst then n else d, 
        if should_jump n jmp then nat a else Suc pc))"

fun eval_machine :: "machine_instruction list \<Rightarrow> machine_state \<Rightarrow> machine_state option" where
  "eval_machine \<Pi> (\<mu>, a, d, pc) = (
    if pc < length \<Pi> 
    then Some (eval_instruction (\<Pi> ! pc) (\<mu>, a, d, pc)) 
    else None)"

end