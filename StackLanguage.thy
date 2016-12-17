theory StackLanguage
imports BasicComputation
begin

datatype stack_instruction = 
  Add | Sub | Neg | Eq | Gt | Lt | And | Or | Not
| Print

type_synonym stack_program = "code_label \<rightharpoonup> stack_instruction list"

type_synonym stack_state = "int list \<times> stack_instruction list \<times> output" (* \<sigma>, \<pi>, \<omega> *)

fun eval_stack :: "stack_program \<Rightarrow> stack_state \<Rightarrow> stack_state option" where
  "eval_stack \<Pi> (i1 # i2 # \<sigma>, Add # \<pi>, \<omega>) = Some ((i2 + i1) # \<sigma>, \<pi>, \<omega>)"
| "eval_stack \<Pi> (i1 # i2 # \<sigma>, Sub # \<pi>, \<omega>) = Some ((i2 - i1) # \<sigma>, \<pi>, \<omega>)"
| "eval_stack \<Pi> (i1 # \<sigma>, Neg # \<pi>, \<omega>) = Some ((-i1) # \<sigma>, \<pi>, \<omega>)"
| "eval_stack \<Pi> (i1 # i2 # \<sigma>, Eq # \<pi>, \<omega>) = Some (unboolify (i2 = i1) # \<sigma>, \<pi>, \<omega>)"
| "eval_stack \<Pi> (i1 # i2 # \<sigma>, Gt # \<pi>, \<omega>) = Some (unboolify (i2 > i1) # \<sigma>, \<pi>, \<omega>)"
| "eval_stack \<Pi> (i1 # i2 # \<sigma>, Lt # \<pi>, \<omega>) = Some (unboolify (i2 < i1) # \<sigma>, \<pi>, \<omega>)"
| "eval_stack \<Pi> (i1 # i2 # \<sigma>, And # \<pi>, \<omega>) = Some (unboolify (boolify i2 \<and> boolify i1) # \<sigma>, \<pi>, \<omega>)"
| "eval_stack \<Pi> (i1 # i2 # \<sigma>, Or # \<pi>, \<omega>) = Some (unboolify (boolify i2 \<or> boolify i1) # \<sigma>, \<pi>, \<omega>)"
| "eval_stack \<Pi> (i1 # \<sigma>, Not # \<pi>, \<omega>) = Some (unboolify (\<not> boolify i1) # \<sigma>, \<pi>, \<omega>)"
| "eval_stack \<Pi> (i1 # \<sigma>, Print # \<pi>, \<omega>) = Some (\<sigma>, \<pi>, i1 # \<omega>)"
| "eval_stack \<Pi> \<Sigma> = None"

fun stack_output :: "stack_state \<Rightarrow> output" where
  "stack_output (\<sigma>, \<pi>, \<omega>) = \<omega>"

end