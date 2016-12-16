theory StackLanguage
imports BasicComputation FiniteMap
begin

datatype stack_instruction = 
  Add | Sub | Neg | Eq | Gt | Lt | And | Or | Not

type_synonym stack_program = "symbol \<leadsto> stack_instruction list"

type_synonym stack_state = "int list \<times> stack_instruction list" (* \<sigma>, \<pi> *)

fun eval_stack :: "stack_program \<Rightarrow> stack_state \<Rightarrow> stack_state option" where
  "eval_stack \<Pi> (i1 # i2 # \<sigma>, Add # \<pi>) = Some ((i2 + i1) # \<sigma>, \<pi>)"
| "eval_stack \<Pi> (i1 # i2 # \<sigma>, Sub # \<pi>) = Some ((i2 - i1) # \<sigma>, \<pi>)"
| "eval_stack \<Pi> (i1 # \<sigma>, Neg # \<pi>) = Some ((-i1) # \<sigma>, \<pi>)"
| "eval_stack \<Pi> (i1 # i2 # \<sigma>, Eq # \<pi>) = Some (unboolify (i2 = i1) # \<sigma>, \<pi>)"
| "eval_stack \<Pi> (i1 # i2 # \<sigma>, Gt # \<pi>) = Some (unboolify (i2 > i1) # \<sigma>, \<pi>)"
| "eval_stack \<Pi> (i1 # i2 # \<sigma>, Lt # \<pi>) = Some (unboolify (i2 < i1) # \<sigma>, \<pi>)"
| "eval_stack \<Pi> (i1 # i2 # \<sigma>, And # \<pi>) = Some (unboolify (boolify i2 \<and> boolify i1) # \<sigma>, \<pi>)"
| "eval_stack \<Pi> (i1 # i2 # \<sigma>, Or # \<pi>) = Some (unboolify (boolify i2 \<or> boolify i1) # \<sigma>, \<pi>)"
| "eval_stack \<Pi> (i1 # \<sigma>, Not # \<pi>) = Some (unboolify (\<not> boolify i1) # \<sigma>, \<pi>)"
| "eval_stack \<Pi> \<Sigma> = None"

end