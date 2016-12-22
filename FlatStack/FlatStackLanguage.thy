theory FlatStackLanguage
imports "../Utilities/BasicComputation"
begin

datatype flat_stack_instruction = 
  FAdd | FSub | FNeg | FEq | FGt | FLt | FAnd | FOr | FNot
| FPrint

type_synonym flat_stack_program = "code_label \<rightharpoonup> flat_stack_instruction list \<times> code_label"

type_synonym flat_stack_state = "int list \<times> flat_stack_instruction list \<times> code_label \<times> output" 
  (* \<sigma>, \<pi>, s, \<omega> *)

fun eval_flat_stack :: "flat_stack_program \<Rightarrow> flat_stack_state \<Rightarrow> flat_stack_state option" where
  "eval_flat_stack \<Pi> (\<sigma>, [], s, \<omega>) = (case \<Pi> s of
      Some (\<pi>, s') \<Rightarrow> Some (\<sigma>, \<pi>, s', \<omega>)
    | None \<Rightarrow> None)"
| "eval_flat_stack \<Pi> (i1 # i2 # \<sigma>, FAdd # \<pi>, s, \<omega>) = Some ((i2 + i1) # \<sigma>, \<pi>, s, \<omega>)"
| "eval_flat_stack \<Pi> (i1 # i2 # \<sigma>, FSub # \<pi>, s, \<omega>) = Some ((i2 - i1) # \<sigma>, \<pi>, s, \<omega>)"
| "eval_flat_stack \<Pi> (i1 # \<sigma>, FNeg # \<pi>, s, \<omega>) = Some ((-i1) # \<sigma>, \<pi>, s, \<omega>)"
| "eval_flat_stack \<Pi> (i1 # i2 # \<sigma>, FEq # \<pi>, s, \<omega>) = Some (unboolify (i2 = i1) # \<sigma>, \<pi>, s, \<omega>)"
| "eval_flat_stack \<Pi> (i1 # i2 # \<sigma>, FGt # \<pi>, s, \<omega>) = Some (unboolify (i2 > i1) # \<sigma>, \<pi>, s, \<omega>)"
| "eval_flat_stack \<Pi> (i1 # i2 # \<sigma>, FLt # \<pi>, s, \<omega>) = Some (unboolify (i2 < i1) # \<sigma>, \<pi>, s, \<omega>)"
| "eval_flat_stack \<Pi> (i1 # i2 # \<sigma>, FAnd # \<pi>, s, \<omega>) = 
    Some (unboolify (boolify i2 \<and> boolify i1) # \<sigma>, \<pi>, s, \<omega>)"
| "eval_flat_stack \<Pi> (i1 # i2 # \<sigma>, FOr # \<pi>, s, \<omega>) = 
    Some (unboolify (boolify i2 \<or> boolify i1) # \<sigma>, \<pi>, s, \<omega>)"
| "eval_flat_stack \<Pi> (i1 # \<sigma>, FNot # \<pi>, s, \<omega>) = Some (unboolify (\<not> boolify i1) # \<sigma>, \<pi>, s, \<omega>)"
| "eval_flat_stack \<Pi> (i1 # \<sigma>, FPrint # \<pi>, s, \<omega>) = Some (\<sigma>, \<pi>, s, i1 # \<omega>)"
| "eval_flat_stack \<Pi> \<Sigma> = None"

fun flat_stack_output :: "flat_stack_state \<Rightarrow> output" where
  "flat_stack_output (\<sigma>, \<pi>, s, \<omega>) = \<omega>"

end