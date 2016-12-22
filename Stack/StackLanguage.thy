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

inductive eval_stack :: "stack_program \<Rightarrow> stack_state \<Rightarrow> stack_state \<Rightarrow> bool" where
  evs_jump [simp]: "\<Pi> s = Some (\<pi>, s') \<Longrightarrow> eval_stack \<Pi> (\<sigma>, [], s, \<omega>) (\<sigma>, \<pi>, s', \<omega>)"
| evs_add [simp]: "eval_stack \<Pi> (IntV i1 # IntV i2 # \<sigma>, Add # \<pi>, s, \<omega>) (IntV (i1 + i2) # \<sigma>, \<pi>, s, \<omega>)"
| evs_sub [simp]: "eval_stack \<Pi> (IntV i1 # IntV i2 # \<sigma>, Sub # \<pi>, s, \<omega>) (IntV (i2 - i1) # \<sigma>, \<pi>, s, \<omega>)"
| evs_neg [simp]: "eval_stack \<Pi> (IntV i1 # \<sigma>, Neg # \<pi>, s, \<omega>) (IntV (-i1) # \<sigma>, \<pi>, s, \<omega>)"
| evs_eq [simp]: "eval_stack \<Pi> (IntV i1 # IntV i2 # \<sigma>, Eq # \<pi>, s, \<omega>) (Bool (i2 = i1) # \<sigma>, \<pi>, s, \<omega>)"
| evs_gt [simp]: "eval_stack \<Pi> (IntV i1 # IntV i2 # \<sigma>, Gt # \<pi>, s, \<omega>) (Bool (i2 > i1) # \<sigma>, \<pi>, s, \<omega>)"
| evs_lt [simp]: "eval_stack \<Pi> (IntV i1 # IntV i2 # \<sigma>, Lt # \<pi>, s, \<omega>) (Bool (i2 < i1) # \<sigma>, \<pi>, s, \<omega>)"
| evs_and [simp]: "eval_stack \<Pi> (Bool i1 # Bool i2 # \<sigma>, And # \<pi>, s, \<omega>) (Bool (i2 \<and> i1) # \<sigma>, \<pi>, s, \<omega>)"
| evs_or [simp]: "eval_stack \<Pi> (Bool i1 # Bool i2 # \<sigma>, Or # \<pi>, s, \<omega>) (Bool (i2 \<or> i1) # \<sigma>, \<pi>, s, \<omega>)"
| evs_not [simp]: "eval_stack \<Pi> (Bool i1 # \<sigma>, Not # \<pi>, s, \<omega>) (Bool (\<not> i1) # \<sigma>, \<pi>, s, \<omega>)"
| evs_print [simp]: "eval_stack \<Pi> (IntV i1 # \<sigma>, Print # \<pi>, s, \<omega>) (\<sigma>, \<pi>, s, i1 # \<omega>)"

fun stack_output :: "stack_state \<Rightarrow> output" where
  "stack_output (\<sigma>, \<pi>, s, \<omega>) = \<omega>"

end