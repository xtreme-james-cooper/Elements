theory StackLanguage
imports BasicComputation
begin

datatype stack_instruction = 
  Add | Sub | Neg | Eq | Gt | Lt | And | Or | Not
| Print

type_synonym stack_program = "code_label \<rightharpoonup> stack_instruction list \<times> code_label"

type_synonym stack_state = "int list \<times> stack_instruction list \<times> code_label \<times> output" 
  (* \<sigma>, \<pi>, s, \<omega> *)

fun eval_stack :: "stack_program \<Rightarrow> stack_state \<Rightarrow> stack_state option" where
  "eval_stack \<Pi> (\<sigma>, [], s, \<omega>) = (case \<Pi> s of
      Some (\<pi>, s') \<Rightarrow> Some (\<sigma>, \<pi>, s', \<omega>)
    | None \<Rightarrow> None)"
| "eval_stack \<Pi> (i1 # i2 # \<sigma>, Add # \<pi>, s, \<omega>) = Some ((i2 + i1) # \<sigma>, \<pi>, s, \<omega>)"
| "eval_stack \<Pi> (i1 # i2 # \<sigma>, Sub # \<pi>, s, \<omega>) = Some ((i2 - i1) # \<sigma>, \<pi>, s, \<omega>)"
| "eval_stack \<Pi> (i1 # \<sigma>, Neg # \<pi>, s, \<omega>) = Some ((-i1) # \<sigma>, \<pi>, s, \<omega>)"
| "eval_stack \<Pi> (i1 # i2 # \<sigma>, Eq # \<pi>, s, \<omega>) = Some (unboolify (i2 = i1) # \<sigma>, \<pi>, s, \<omega>)"
| "eval_stack \<Pi> (i1 # i2 # \<sigma>, Gt # \<pi>, s, \<omega>) = Some (unboolify (i2 > i1) # \<sigma>, \<pi>, s, \<omega>)"
| "eval_stack \<Pi> (i1 # i2 # \<sigma>, Lt # \<pi>, s, \<omega>) = Some (unboolify (i2 < i1) # \<sigma>, \<pi>, s, \<omega>)"
| "eval_stack \<Pi> (i1 # i2 # \<sigma>, And # \<pi>, s, \<omega>) = 
    Some (unboolify (boolify i2 \<and> boolify i1) # \<sigma>, \<pi>, s, \<omega>)"
| "eval_stack \<Pi> (i1 # i2 # \<sigma>, Or # \<pi>, s, \<omega>) = 
    Some (unboolify (boolify i2 \<or> boolify i1) # \<sigma>, \<pi>, s, \<omega>)"
| "eval_stack \<Pi> (i1 # \<sigma>, Not # \<pi>, s, \<omega>) = Some (unboolify (\<not> boolify i1) # \<sigma>, \<pi>, s, \<omega>)"
| "eval_stack \<Pi> (i1 # \<sigma>, Print # \<pi>, s, \<omega>) = Some (\<sigma>, \<pi>, s, i1 # \<omega>)"
| "eval_stack \<Pi> \<Sigma> = None"

fun stack_output :: "stack_state \<Rightarrow> output" where
  "stack_output (\<sigma>, \<pi>, s, \<omega>) = \<omega>"

end