theory MachineLanguage
imports BasicComputation
begin

datatype instruction =
  AInstr int
| CInstr "register set" computation "comparison set"

type_synonym machine_state = "memory \<times> int \<times> int \<times> nat" (* M, A, D, PC *)

fun eval_instruction :: "instruction \<Rightarrow> machine_state \<Rightarrow> machine_state" where
  "eval_instruction (AInstr x) (\<sigma>, a, d, pc) = (\<sigma>, x, d, Suc pc)"
| "eval_instruction (CInstr dst cmp jmp) (\<sigma>, a, d, pc) = (
    let n = compute cmp (\<sigma> a) a d
    in (if M \<in> dst then \<sigma>(a := n) else \<sigma>, 
        if A \<in> dst then n else a, 
        if D \<in> dst then n else d, 
        if should_jump n jmp then nat a else Suc pc))"

fun eval_machine :: "instruction list \<Rightarrow> machine_state \<Rightarrow> machine_state option" where
  "eval_machine \<Pi> (\<sigma>, a, d, pc) = (
    if pc < length \<Pi> 
    then Some (eval_instruction (\<Pi> ! pc) (\<sigma>, a, d, pc)) 
    else None)"

end