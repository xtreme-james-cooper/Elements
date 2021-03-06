theory StackLanguage
imports "../Utilities/BasicComputation" "../Utilities/Iterate"
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

type_synonym stack_code_block = "stack_instruction list \<times> code_label"

record stack_function_def =
  arity :: nat
  local_count :: nat
  main_code :: stack_code_block
  other_code :: "code_label \<rightharpoonup> stack_code_block"
  
type_synonym stack_program = "function_name \<rightharpoonup> stack_function_def"

datatype stack_value =
  IntV int
| Bool bool

record frame = 
  name :: function_name 
  arguments :: "stack_value list"
  locals :: "stack_value list"
  saved_stack :: "stack_value list"
  saved_code :: stack_code_block

type_synonym stack_state = "stack_value list \<times> frame list \<times> stack_code_block \<times> output" 
  (* \<sigma>, \<phi>, \<pi>, \<omega> *)

inductive eval_stack :: "stack_program \<Rightarrow> stack_state \<Rightarrow> stack_state \<Rightarrow> bool" where
  evs_jump [simp]: "\<Pi> (frame.name f) = Some def \<Longrightarrow> stack_function_def.other_code def s = Some \<pi> \<Longrightarrow> 
    eval_stack \<Pi> ([], f # \<phi>, ([], s), \<omega>) ([], f # \<phi>, \<pi>, \<omega>)"
| evs_add [simp]: "eval_stack \<Pi> (IntV i1 # IntV i2 # \<sigma>, \<phi>, (Add # \<pi>, s), \<omega>) 
    (IntV (i1 + i2) # \<sigma>, \<phi>, (\<pi>, s), \<omega>)"
| evs_sub [simp]: "eval_stack \<Pi> (IntV i1 # IntV i2 # \<sigma>, \<phi>, (Sub # \<pi>, s), \<omega>) 
    (IntV (i2 - i1) # \<sigma>, \<phi>, (\<pi>, s), \<omega>)"
| evs_neg [simp]: "eval_stack \<Pi> (IntV i1 # \<sigma>, \<phi>, (Neg # \<pi>, s), \<omega>) (IntV (-i1) # \<sigma>, \<phi>, (\<pi>, s), \<omega>)"
| evs_eq [simp]: "eval_stack \<Pi> (IntV i1 # IntV i2 # \<sigma>, \<phi>, (Eq # \<pi>, s), \<omega>) 
    (Bool (i2 = i1) # \<sigma>, \<phi>, (\<pi>, s), \<omega>)"
| evs_gt [simp]: "eval_stack \<Pi> (IntV i1 # IntV i2 # \<sigma>, \<phi>, (Gt # \<pi>, s), \<omega>) 
    (Bool (i2 > i1) # \<sigma>, \<phi>, (\<pi>, s), \<omega>)"
| evs_lt [simp]: "eval_stack \<Pi> (IntV i1 # IntV i2 # \<sigma>, \<phi>, (Lt # \<pi>, s), \<omega>) 
    (Bool (i2 < i1) # \<sigma>, \<phi>, (\<pi>, s), \<omega>)"
| evs_and [simp]: "eval_stack \<Pi> (Bool i1 # Bool i2 # \<sigma>, \<phi>, (And # \<pi>, s), \<omega>) 
    (Bool (i2 \<and> i1) # \<sigma>, \<phi>, (\<pi>, s), \<omega>)"
| evs_or [simp]: "eval_stack \<Pi> (Bool i1 # Bool i2 # \<sigma>, \<phi>, (Or # \<pi>, s), \<omega>) 
    (Bool (i2 \<or> i1) # \<sigma>, \<phi>, (\<pi>, s), \<omega>)"
| evs_not [simp]: "eval_stack \<Pi> (Bool i1 # \<sigma>, \<phi>, (Not # \<pi>, s), \<omega>) (Bool (\<not> i1) # \<sigma>, \<phi>, (\<pi>, s), \<omega>)"
| evs_push_c [simp]: "eval_stack \<Pi> (\<sigma>, \<phi>, (Push (Constant i) # \<pi>, s), \<omega>) (IntV i # \<sigma>, \<phi>, (\<pi>, s), \<omega>)"
| evs_push_l [simp]: "n < length (frame.locals f) \<Longrightarrow> 
    eval_stack \<Pi> (\<sigma>, f # \<phi>, (Push (Local n) # \<pi>, s), \<omega>) (frame.locals f ! n # \<sigma>, f # \<phi>, (\<pi>, s), \<omega>)"
| evs_push_a [simp]: "n < length (frame.arguments f) \<Longrightarrow> 
    eval_stack \<Pi> (\<sigma>, f # \<phi>, (Push (Argument n) # \<pi>, s), \<omega>) 
      (frame.arguments f ! n # \<sigma>, f # \<phi>, (\<pi>, s), \<omega>)"
| evs_pop_l [simp]: "n < length (frame.locals f) \<Longrightarrow> 
    eval_stack \<Pi> (v # \<sigma>, f # \<phi>, (Pop (Local n) # \<pi>, s), \<omega>) 
      (\<sigma>, f \<lparr> locals := frame.locals f [n := v] \<rparr> # \<phi>, (\<pi>, s), \<omega>)"
| evs_pop_a [simp]: "n < length (frame.arguments f) \<Longrightarrow> 
    eval_stack \<Pi> (v # \<sigma>, f # \<phi>, (Pop (Argument n) # \<pi>, s), \<omega>) 
      (\<sigma>, f \<lparr> arguments := frame.arguments f [n := v] \<rparr> # \<phi>, (\<pi>, s), \<omega>)"
| evs_if_t [simp]: "eval_stack \<Pi> (Bool True # \<sigma>, \<phi>, (IfJ \<pi>\<^sub>t \<pi>\<^sub>f # \<pi>, s), \<omega>) (\<sigma>, \<phi>, (\<pi>\<^sub>t @ \<pi>, s), \<omega>)"
| evs_if_f [simp]: "eval_stack \<Pi> (Bool False # \<sigma>, \<phi>, (IfJ \<pi>\<^sub>t \<pi>\<^sub>f # \<pi>, s), \<omega>) (\<sigma>, \<phi>, (\<pi>\<^sub>f @ \<pi>, s), \<omega>)"
| evs_goto [simp]: "\<Pi> (frame.name f) = Some def \<Longrightarrow> stack_function_def.other_code def s = Some \<pi>' \<Longrightarrow> 
    eval_stack \<Pi> ([], f # \<phi>, (Goto s # \<pi>, _), \<omega>) ([], f # \<phi>, \<pi>', \<omega>)"
| evs_call [simp]: "\<Pi> f = Some def \<Longrightarrow> length \<sigma> \<ge> stack_function_def.arity def \<Longrightarrow> 
    eval_stack \<Pi> (\<sigma>, \<phi>, (Call f # \<pi>', s), \<omega>) ([], \<lparr> 
      name = f, arguments = take (stack_function_def.arity def) \<sigma>, 
      locals = repeat (IntV 0) (stack_function_def.local_count def), 
      saved_stack = (drop (stack_function_def.arity def) \<sigma>), saved_code = (\<pi>', s) \<rparr> # \<phi>, \<pi>, \<omega>)"
| evs_return [simp]: "eval_stack \<Pi> (v # [], f # \<phi>, (Return # \<pi>, s), \<omega>) 
    (v # frame.saved_stack f, \<phi>, frame.saved_code f, \<omega>)"
| evs_print [simp]: "eval_stack \<Pi> (IntV i1 # \<sigma>, \<phi>, (Print # \<pi>, s), \<omega>) (\<sigma>, \<phi>, (\<pi>, s), i1 # \<omega>)"

fun stack_output :: "stack_state \<Rightarrow> output" where
  "stack_output (\<sigma>, \<phi>, \<pi>, \<omega>) = \<omega>"

(* state validity *)

fun valid_frame :: "stack_program \<Rightarrow> frame \<Rightarrow> bool" where
  "valid_frame \<Pi> \<lparr> name = f, arguments = as, locals = ls, saved_stack = \<sigma>, saved_code = \<pi> \<rparr> = (
    case \<Pi> f of
        Some def \<Rightarrow> length as = stack_function_def.arity def \<and> 
          length ls = stack_function_def.local_count def
      | None \<Rightarrow> False)"

fun valid_state :: "stack_program \<Rightarrow> stack_state \<Rightarrow> bool" where
  "valid_state \<Pi> (\<sigma>, \<phi>, \<pi>, \<omega>) = (\<forall>f \<in> set \<phi>. valid_frame \<Pi> f)"

lemma [simp]: "valid_frame \<Pi> fr \<Longrightarrow> valid_frame \<Pi> (fr\<lparr>locals := locals fr[n := v]\<rparr>)"
  by (cases fr) (auto split: option.splits)

lemma [simp]: "valid_frame \<Pi> fr \<Longrightarrow> valid_frame \<Pi> (fr\<lparr>arguments := arguments fr[n := v]\<rparr>)"
  by (cases fr) (auto split: option.splits)

lemma [simp]: "valid_frame \<Pi> fr \<Longrightarrow> \<Pi> (frame.name fr) = Some def \<Longrightarrow> 
    length (frame.locals fr) = stack_function_def.local_count def"
  by (cases fr) simp

lemma [simp]: "eval_stack \<Pi> \<Sigma> \<Sigma>' \<Longrightarrow> valid_state \<Pi> \<Sigma> \<Longrightarrow> valid_state \<Pi> \<Sigma>'"
  by (induction \<Pi> \<Sigma> \<Sigma>' rule: eval_stack.induct) simp_all

lemma [simp]: "iterate_ind (eval_stack \<Pi>) \<Sigma> \<Sigma>' \<Longrightarrow> valid_state \<Pi> \<Sigma> \<Longrightarrow> valid_state \<Pi> \<Sigma>'"
  by (induction "eval_stack \<Pi>" \<Sigma> \<Sigma>' rule: iterate_ind.induct) simp_all

end