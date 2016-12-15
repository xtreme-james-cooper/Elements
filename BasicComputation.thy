theory BasicComputation
imports Main
begin

type_synonym memory = "int \<Rightarrow> int"

datatype register = A | D | M

datatype comparison = LT | EQ | GT

datatype computation = 
  Zero | One | NegOne | Reg register | Not register | Neg register | Incr register | Decr register 
| DPlusA | DPlusM | DMinusA | DMinusM | AMinusD | MMinusD | DAndA | DAndM | DOrA | DOrM

fun should_jump :: "int \<Rightarrow> comparison set \<Rightarrow> bool" where
  "should_jump n jmp = ((LT \<in> jmp \<and> n < 0) \<or> (EQ \<in> jmp \<and> n = 0) \<or> (GT \<in> jmp \<and> n > 0 ))"

definition boolify :: "int \<Rightarrow> bool" where
  "boolify i = (i = 0)"

definition unboolify :: "bool \<Rightarrow> int" where
  "unboolify b = (if b then 1 else 0)"

fun compute :: "computation \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "compute Zero m a d = 0"
| "compute One m a d = 1"
| "compute NegOne m a d = -1"
| "compute (Reg M) m a d = m"
| "compute (Reg A) m a d = a"
| "compute (Reg D) m a d = d"
| "compute (Not M) m a d = unboolify (\<not> boolify m)"
| "compute (Not A) m a d = unboolify (\<not> boolify a)"
| "compute (Not D) m a d = unboolify (\<not> boolify d)"
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
| "compute DAndA m a d = unboolify (boolify d \<and> boolify a)"
| "compute DAndM m a d = unboolify (boolify d \<and> boolify m)"
| "compute DOrA m a d = unboolify (boolify d \<or> boolify a)"
| "compute DOrM m a d = unboolify (boolify d \<or> boolify m)"

end