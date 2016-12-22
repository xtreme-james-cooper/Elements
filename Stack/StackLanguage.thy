theory StackLanguage
imports "../Utilities/BasicComputation"
begin

datatype address = 
  Constant int
| Local nat
| Argument nat

datatype stack_instruction = 
  Add | Sub | Neg | Eq | Gt | Lt | And | Or | Not
| Push address | Pop address
| Print

type_synonym stack_program = "code_label \<rightharpoonup> stack_instruction list \<times> code_label"

datatype stack_value =
  IntV int
| Bool bool

datatype frame = Frame "stack_value list" "stack_value list"

type_synonym stack_state = 
  "stack_value list \<times> frame list \<times> stack_instruction list \<times> code_label \<times> output" 
  (* \<sigma>, \<phi>, \<pi>, s, \<omega> *)

inductive eval_stack :: "stack_program \<Rightarrow> stack_state \<Rightarrow> stack_state \<Rightarrow> bool" where
  evs_jump [simp]: "\<Pi> s = Some (\<pi>, s') \<Longrightarrow> eval_stack \<Pi> (\<sigma>, \<phi>, [], s, \<omega>) (\<sigma>, \<phi>, \<pi>, s', \<omega>)"
| evs_add [simp]: "eval_stack \<Pi> (IntV i1 # IntV i2 # \<sigma>, \<phi>, Add # \<pi>, s, \<omega>) 
    (IntV (i1 + i2) # \<sigma>, \<phi>, \<pi>, s, \<omega>)"
| evs_sub [simp]: "eval_stack \<Pi> (IntV i1 # IntV i2 # \<sigma>, \<phi>, Sub # \<pi>, s, \<omega>) 
    (IntV (i2 - i1) # \<sigma>, \<phi>, \<pi>, s, \<omega>)"
| evs_neg [simp]: "eval_stack \<Pi> (IntV i1 # \<sigma>, \<phi>, Neg # \<pi>, s, \<omega>) (IntV (-i1) # \<sigma>, \<phi>, \<pi>, s, \<omega>)"
| evs_eq [simp]: "eval_stack \<Pi> (IntV i1 # IntV i2 # \<sigma>, \<phi>, Eq # \<pi>, s, \<omega>) 
    (Bool (i2 = i1) # \<sigma>, \<phi>, \<pi>, s, \<omega>)"
| evs_gt [simp]: "eval_stack \<Pi> (IntV i1 # IntV i2 # \<sigma>, \<phi>, Gt # \<pi>, s, \<omega>) 
    (Bool (i2 > i1) # \<sigma>, \<phi>, \<pi>, s, \<omega>)"
| evs_lt [simp]: "eval_stack \<Pi> (IntV i1 # IntV i2 # \<sigma>, \<phi>, Lt # \<pi>, s, \<omega>) 
    (Bool (i2 < i1) # \<sigma>, \<phi>, \<pi>, s, \<omega>)"
| evs_and [simp]: "eval_stack \<Pi> (Bool i1 # Bool i2 # \<sigma>, \<phi>, And # \<pi>, s, \<omega>) 
    (Bool (i2 \<and> i1) # \<sigma>, \<phi>, \<pi>, s, \<omega>)"
| evs_or [simp]: "eval_stack \<Pi> (Bool i1 # Bool i2 # \<sigma>, \<phi>, Or # \<pi>, s, \<omega>) 
    (Bool (i2 \<or> i1) # \<sigma>, \<phi>, \<pi>, s, \<omega>)"
| evs_not [simp]: "eval_stack \<Pi> (Bool i1 # \<sigma>, \<phi>, Not # \<pi>, s, \<omega>) (Bool (\<not> i1) # \<sigma>, \<phi>, \<pi>, s, \<omega>)"
| evs_push_c [simp]: "eval_stack \<Pi> (\<sigma>, \<phi>, Push (Constant i) # \<pi>, s, \<omega>) (IntV i # \<sigma>, \<phi>, \<pi>, s, \<omega>)"
| evs_push_l [simp]: "eval_stack \<Pi> (\<sigma>, Frame as ls # \<phi>, Push (Local n) # \<pi>, s, \<omega>) 
    (ls ! n # \<sigma>, \<phi>, \<pi>, s, \<omega>)"
| evs_push_a [simp]: "eval_stack \<Pi> (\<sigma>, Frame as ls # \<phi>, Push (Argument n) # \<pi>, s, \<omega>) 
    (as ! n # \<sigma>, \<phi>, \<pi>, s, \<omega>)"
| evs_pop_l [simp]: "eval_stack \<Pi> (v # \<sigma>, Frame as ls # \<phi>, Pop (Local n) # \<pi>, s, \<omega>) 
    (\<sigma>, Frame as (update_list ls v n) # \<phi>, \<pi>, s, \<omega>)"
| evs_pop_a [simp]: "eval_stack \<Pi> (v # \<sigma>, Frame as ls # \<phi>, Pop (Argument n) # \<pi>, s, \<omega>) 
    (\<sigma>, Frame (update_list as v n) ls # \<phi>, \<pi>, s, \<omega>)"
| evs_print [simp]: "eval_stack \<Pi> (IntV i1 # \<sigma>, \<phi>, Print # \<pi>, s, \<omega>) (\<sigma>, \<phi>, \<pi>, s, i1 # \<omega>)"

fun stack_output :: "stack_state \<Rightarrow> output" where
  "stack_output (\<sigma>, \<phi>, \<pi>, s, \<omega>) = \<omega>"

end