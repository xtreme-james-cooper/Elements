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
| IfJ "stack_instruction list" "stack_instruction list" 
| Goto code_label
| Call function_name
| Return
| Print

type_synonym stack_program = 
  "function_name \<rightharpoonup> nat \<times> nat \<times> (code_label \<rightharpoonup> stack_instruction list \<times> code_label)"

datatype stack_value =
  IntV int
| Bool bool

datatype frame = Frame function_name 
  "stack_value list" (* arguments *)
  "stack_value list" (* local variables *)
  "stack_value list" (* saved stack *)

type_synonym stack_state = 
  "stack_value list \<times> frame list \<times> stack_instruction list \<times> code_label \<times> output" 
  (* \<sigma>, \<phi>, \<pi>, s, \<omega> *)

inductive eval_stack :: "stack_program \<Rightarrow> stack_state \<Rightarrow> stack_state \<Rightarrow> bool" where
  evs_jump [simp]: "\<Pi> f = Some (a, l, \<Phi>) \<Longrightarrow> \<Phi> s = Some (\<pi>, s') \<Longrightarrow> 
    eval_stack \<Pi> (\<sigma>, Frame f as ls \<sigma>' # \<phi>, [], s, \<omega>) (\<sigma>, Frame f as ls \<sigma>' # \<phi>, \<pi>, s', \<omega>)"
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
| evs_push_l [simp]: "eval_stack \<Pi> (\<sigma>, Frame f as ls \<sigma>' # \<phi>, Push (Local n) # \<pi>, s, \<omega>) 
    (ls ! n # \<sigma>, Frame f as ls \<sigma>' # \<phi>, \<pi>, s, \<omega>)"
| evs_push_a [simp]: "eval_stack \<Pi> (\<sigma>, Frame f as ls \<sigma>' # \<phi>, Push (Argument n) # \<pi>, s, \<omega>) 
    (as ! n # \<sigma>, Frame f as ls \<sigma>' # \<phi>, \<pi>, s, \<omega>)"
| evs_pop_l [simp]: "eval_stack \<Pi> (v # \<sigma>, Frame f as ls \<sigma>' # \<phi>, Pop (Local n) # \<pi>, s, \<omega>) 
    (\<sigma>, Frame f as (ls[n := v]) \<sigma>' # \<phi>, \<pi>, s, \<omega>)"
| evs_pop_a [simp]: "eval_stack \<Pi> (v # \<sigma>, Frame f as ls \<sigma>' # \<phi>, Pop (Argument n) # \<pi>, s, \<omega>) 
    (\<sigma>, Frame f (as[n := v]) ls \<sigma>' # \<phi>, \<pi>, s, \<omega>)"
| evs_if_t [simp]: "eval_stack \<Pi> (Bool True # \<sigma>, \<phi>, IfJ \<pi>\<^sub>t \<pi>\<^sub>f # \<pi>, s, \<omega>) (\<sigma>, \<phi>, \<pi>\<^sub>t @ \<pi>, s, \<omega>)"
| evs_if_f [simp]: "eval_stack \<Pi> (Bool False # \<sigma>, \<phi>, IfJ \<pi>\<^sub>t \<pi>\<^sub>f # \<pi>, s, \<omega>) (\<sigma>, \<phi>, \<pi>\<^sub>f @ \<pi>, s, \<omega>)"
| evs_goto [simp]: "\<Pi> f = Some (a, l, \<Phi>) \<Longrightarrow> \<Phi> s = Some (\<pi>, s') \<Longrightarrow> 
    eval_stack \<Pi> (\<sigma>, Frame f as ls \<sigma>' # \<phi>, Goto s # \<pi>, s'', \<omega>) (\<sigma>, Frame f as ls \<sigma>' # \<phi>, \<pi>', s', \<omega>)"
| evs_call [simp]: "\<Pi> f = Some (a, l, \<Phi>) \<Longrightarrow> 
    eval_stack \<Pi> (\<sigma>, \<phi>, Call f # \<pi>, s, \<omega>) ([], Frame f (take a \<sigma>) 
      (repeat (IntV 0) l) (drop a \<sigma>) # \<phi>, \<pi>, s, \<omega>)"
| evs_return [simp]: 
    "eval_stack \<Pi> (v # \<sigma>, Frame f as ls \<sigma>' # \<phi>, Return # \<pi>, s, \<omega>) (v # \<sigma>', \<phi>, \<pi>, s, \<omega>)"
| evs_print [simp]: "eval_stack \<Pi> (IntV i1 # \<sigma>, \<phi>, Print # \<pi>, s, \<omega>) (\<sigma>, \<phi>, \<pi>, s, i1 # \<omega>)"

fun stack_output :: "stack_state \<Rightarrow> output" where
  "stack_output (\<sigma>, \<phi>, \<pi>, s, \<omega>) = \<omega>"

end