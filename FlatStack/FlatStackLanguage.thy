theory FlatStackLanguage
imports "../Utilities/BasicComputation"
begin

datatype flat_stack_instruction = 
  FAdd | FSub | FNeg | FEq | FGt | FLt | FAnd | FOr | FNot
| Dup nat | Upd nat
| FPrint

type_synonym flat_stack_program = "code_label \<rightharpoonup> flat_stack_instruction list \<times> code_label"

type_synonym flat_stack_state = "int list \<times> flat_stack_instruction list \<times> code_label \<times> output" 
  (* \<sigma>, \<pi>, s, \<omega> *)

inductive eval_flat_stack :: "flat_stack_program \<Rightarrow> flat_stack_state \<Rightarrow> flat_stack_state \<Rightarrow> bool" where
  evf_jump [simp]: "\<Pi> s = Some (\<pi>, s') \<Longrightarrow> eval_flat_stack \<Pi> (\<sigma>, [], s, \<omega>) (\<sigma>, \<pi>, s', \<omega>)"
| evf_add [simp]: "eval_flat_stack \<Pi> (i1 # i2 # \<sigma>, FAdd # \<pi>, s, \<omega>) ((i1 + i2) # \<sigma>, \<pi>, s, \<omega>)"
| evf_sub [simp]: "eval_flat_stack \<Pi> (i1 # i2 # \<sigma>, FSub # \<pi>, s, \<omega>) ((i2 - i1) # \<sigma>, \<pi>, s, \<omega>)"
| evf_neg [simp]: "eval_flat_stack \<Pi> (i1 # \<sigma>, FNeg # \<pi>, s, \<omega>) ((-i1) # \<sigma>, \<pi>, s, \<omega>)"
| evf_eq [simp]: "eval_flat_stack \<Pi> (i1 # i2 # \<sigma>, FEq # \<pi>, s, \<omega>) (unboolify (i2 = i1) # \<sigma>, \<pi>, s, \<omega>)"
| evf_gt [simp]: "eval_flat_stack \<Pi> (i1 # i2 # \<sigma>, FGt # \<pi>, s, \<omega>) (unboolify (i2 > i1) # \<sigma>, \<pi>, s, \<omega>)"
| evf_lt [simp]: "eval_flat_stack \<Pi> (i1 # i2 # \<sigma>, FLt # \<pi>, s, \<omega>) (unboolify (i2 < i1) # \<sigma>, \<pi>, s, \<omega>)"
| evf_and [simp]: "eval_flat_stack \<Pi> (i1 # i2 # \<sigma>, FAnd # \<pi>, s, \<omega>) 
    (unboolify (boolify i1 \<and> boolify i2) # \<sigma>, \<pi>, s, \<omega>)"
| evf_or [simp]: "eval_flat_stack \<Pi> (i1 # i2 # \<sigma>, FOr # \<pi>, s, \<omega>) 
    (unboolify (boolify i1 \<or> boolify i2) # \<sigma>, \<pi>, s, \<omega>)"
| evf_not [simp]: "eval_flat_stack \<Pi> (i1 # \<sigma>, FNot # \<pi>, s, \<omega>) 
    (unboolify (\<not> boolify i1) # \<sigma>, \<pi>, s, \<omega>)"
| evf_dup [simp]: "n < length \<sigma> \<Longrightarrow> eval_flat_stack \<Pi> (\<sigma>, Dup n # \<pi>, s, \<omega>) 
    (\<sigma> ! n # \<sigma>, \<pi>, s, \<omega>)"
| evf_upd [simp]: "n < length \<sigma> \<Longrightarrow> eval_flat_stack \<Pi> (i1 # \<sigma>, Upd n # \<pi>, s, \<omega>) 
    (\<sigma>[n := i1], \<pi>, s, \<omega>)"
| evf_print [simp]: "eval_flat_stack \<Pi> (i1 # \<sigma>, FPrint # \<pi>, s, \<omega>) (\<sigma>, \<pi>, s, i1 # \<omega>)"

fun flat_stack_output :: "flat_stack_state \<Rightarrow> output" where
  "flat_stack_output (\<sigma>, \<pi>, s, \<omega>) = \<omega>"

end