theory MachineLanguage
imports Main
begin

type_synonym memory = "int \<Rightarrow> int"

datatype register = A | D | M

datatype comparison = LT | EQ | GT

datatype computation = 
  Zero | One | NegOne | Reg register | Not register | Neg register | Incr register | Decr register 
| DPlusA | DPlusM | DMinusA | DMinusM | AMinusD | MMinusD | DAndA | DAndM | DOrA | DOrM

datatype instruction =
  AInstr int
| CInstr "register set" computation "comparison set"

type_synonym machine_state = "memory \<times> int \<times> int \<times> nat" (* M, A, D, PC *)

fun should_jump :: "int \<Rightarrow> comparison set \<Rightarrow> bool" where
  "should_jump n jmp = ((LT \<in> jmp \<and> n < 0) \<or> (EQ \<in> jmp \<and> n = 0) \<or> (GT \<in> jmp \<and> n > 0 ))"

fun compute :: "computation \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "compute Zero m a d = 0"
| "compute One m a d = 1"
| "compute NegOne m a d = -1"
| "compute (Reg M) m a d = m"
| "compute (Reg A) m a d = a"
| "compute (Reg D) m a d = d"
| "compute (Not M) m a d = (if m = 0 then 1 else 0)"
| "compute (Not A) m a d = (if a = 0 then 1 else 0)"
| "compute (Not D) m a d = (if d = 0 then 1 else 0)"
| "compute (Neg M) m a d = -m"
| "compute (Neg A) m a d = -a"
| "compute (Neg D) m a d = -d"
| "compute (Incr M) m a d = m + 1"
| "compute (Incr A) m a d = a + 1"
| "compute (Incr D) m a d = d + 1"
| "compute (Decr M) m a d = m - 1"
| "compute (Decr A) m a d = a - 1"
| "compute (Decr D) m a d = d - 1"
| "compute DPlusA m a d = d + a"
| "compute DPlusM m a d = d + m"
| "compute DMinusA m a d = d - a"
| "compute DMinusM m a d = d - m"
| "compute AMinusD m a d = a - d"
| "compute MMinusD m a d = m - d"
| "compute DAndA m a d = (if d \<noteq> 0 \<and> a \<noteq> 0 then 1 else 0)"
| "compute DAndM m a d = (if d \<noteq> 0 \<and> m \<noteq> 0 then 1 else 0)"
| "compute DOrA m a d = (if d \<noteq> 0 \<or> a \<noteq> 0 then 1 else 0)"
| "compute DOrM m a d = (if d \<noteq> 0 \<or> m \<noteq> 0 then 1 else 0)"

fun eval_instruction :: "instruction \<Rightarrow> machine_state \<Rightarrow> machine_state" where
  "eval_instruction (AInstr x) (\<sigma>, a, d, pc) = (\<sigma>, x, d, Suc pc)"
| "eval_instruction (CInstr dst cmp jmp) (\<sigma>, a, d, pc) = (
    let n = compute cmp (\<sigma> a) a d
    in (if M \<in> dst then \<sigma>(a := n) else \<sigma>, 
        if A \<in> dst then n else a, 
        if D \<in> dst then n else d, 
        if should_jump n jmp then nat a else Suc pc))"

fun eval :: "instruction list \<Rightarrow> machine_state \<Rightarrow> machine_state option" where
  "eval \<Pi> (\<sigma>, a, d, pc) = (
    if pc < length \<Pi> 
    then Some (eval_instruction (\<Pi> ! pc) (\<sigma>, a, d, pc)) 
    else None)"

end