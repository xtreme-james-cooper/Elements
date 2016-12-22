theory StackLanguage
imports "../Utilities/BasicComputation"
begin

datatype stack_instruction = 
  Add | Sub | Neg | Eq | Gt | Lt | And | Or | Not
| Print

type_synonym stack_program = "code_label \<rightharpoonup> stack_instruction list \<times> code_label"

datatype stack_value =
  IntV int
| Bool bool

type_synonym stack_state = "stack_value list \<times> stack_instruction list \<times> code_label \<times> output" 
  (* \<sigma>, \<pi>, s, \<omega> *)

fun eval_stack :: "stack_program \<Rightarrow> stack_state \<Rightarrow> stack_state option" where
  "eval_stack \<Pi> (\<sigma>, [], s, \<omega>) = (case \<Pi> s of
      Some (\<pi>, s') \<Rightarrow> Some (\<sigma>, \<pi>, s', \<omega>)
    | None \<Rightarrow> None)"
| "eval_stack \<Pi> (IntV i1 # IntV i2 # \<sigma>, Add # \<pi>, s, \<omega>) = Some (IntV (i2 + i1) # \<sigma>, \<pi>, s, \<omega>)"
| "eval_stack \<Pi> (IntV i1 # IntV i2 # \<sigma>, Sub # \<pi>, s, \<omega>) = Some (IntV (i2 - i1) # \<sigma>, \<pi>, s, \<omega>)"
| "eval_stack \<Pi> (IntV i1 # \<sigma>, Neg # \<pi>, s, \<omega>) = Some (IntV (-i1) # \<sigma>, \<pi>, s, \<omega>)"
| "eval_stack \<Pi> (IntV i1 # IntV i2 # \<sigma>, Eq # \<pi>, s, \<omega>) = Some (Bool (i2 = i1) # \<sigma>, \<pi>, s, \<omega>)"
| "eval_stack \<Pi> (IntV i1 # IntV i2 # \<sigma>, Gt # \<pi>, s, \<omega>) = Some (Bool (i2 > i1) # \<sigma>, \<pi>, s, \<omega>)"
| "eval_stack \<Pi> (IntV i1 # IntV i2 # \<sigma>, Lt # \<pi>, s, \<omega>) = Some (Bool (i2 < i1) # \<sigma>, \<pi>, s, \<omega>)"
| "eval_stack \<Pi> (Bool i1 # Bool i2 # \<sigma>, And # \<pi>, s, \<omega>) = Some (Bool (i2 \<and> i1) # \<sigma>, \<pi>, s, \<omega>)"
| "eval_stack \<Pi> (Bool i1 # Bool i2 # \<sigma>, Or # \<pi>, s, \<omega>) = Some (Bool (i2 \<or> i1) # \<sigma>, \<pi>, s, \<omega>)"
| "eval_stack \<Pi> (Bool i1 # \<sigma>, Not # \<pi>, s, \<omega>) = Some (Bool (\<not> i1) # \<sigma>, \<pi>, s, \<omega>)"
| "eval_stack \<Pi> (IntV i1 # \<sigma>, Print # \<pi>, s, \<omega>) = Some (\<sigma>, \<pi>, s, i1 # \<omega>)"
| "eval_stack \<Pi> \<Sigma> = None"

fun stack_output :: "stack_state \<Rightarrow> output" where
  "stack_output (\<sigma>, \<pi>, s, \<omega>) = \<omega>"

end