theory Flattening
imports StackLanguage "../FlatStack/FlatStackLanguage" "../Utilities/Iterate"
begin

primrec instruction_convert :: "stack_instruction \<Rightarrow> flat_stack_instruction" where
  "instruction_convert Add = FAdd"
| "instruction_convert Sub = FSub"
| "instruction_convert Neg = FNeg"
| "instruction_convert Eq = FEq"
| "instruction_convert Gt = FGt"
| "instruction_convert Lt = FLt"
| "instruction_convert And = FAnd"
| "instruction_convert Or = FOr"
| "instruction_convert Not = FNot"
| "instruction_convert Print = FPrint"

primrec stack_value_convert :: "stack_value \<Rightarrow> int" where
  "stack_value_convert (IntV i) = i"
| "stack_value_convert (Bool b) = unboolify b"

definition flatten :: "stack_program \<Rightarrow> flat_stack_program" where
  "flatten \<Pi> = map_option (\<lambda>(\<pi>, s). (map instruction_convert \<pi>, s)) o \<Pi>"

fun state_convert :: "stack_state \<Rightarrow> flat_stack_state" where
  "state_convert (\<sigma>, \<pi>, s, \<omega>) = (map stack_value_convert \<sigma>, map instruction_convert \<pi>, s, \<omega>)"

(* flattening correct *)

lemma [simp]: "flat_stack_output (state_convert \<Sigma>\<^sub>S) = stack_output \<Sigma>\<^sub>S"
  by (induction \<Sigma>\<^sub>S rule: state_convert.induct) simp

lemma [simp]: "finite (dom \<Pi>) \<Longrightarrow> finite (dom (flatten \<Pi>))"
  by (simp add: flatten_def)

lemma [simp]: "\<Pi> s = Some (\<pi>, s') \<Longrightarrow> flatten \<Pi> s = Some (map instruction_convert \<pi>, s')"
  by (simp add: flatten_def)

lemma [simp]: "eval_stack \<Pi> \<Sigma> = Some \<Sigma>' \<Longrightarrow> 
    eval_flat_stack (flatten \<Pi>) (state_convert \<Sigma>) = Some (state_convert \<Sigma>')"
  proof (induction \<Pi> \<Sigma> rule: eval_stack.induct)
  case (1 \<Pi> \<sigma> s \<omega>) 
    thus ?case by (cases \<Sigma>', cases "\<Pi> s") auto
  next case 2
    thus ?case by (cases \<Sigma>') auto
  next case 3
    thus ?case by (cases \<Sigma>') auto
  next case 4
    thus ?case by (cases \<Sigma>') auto
  next case 5
    thus ?case by (cases \<Sigma>') auto
  next case 6
    thus ?case by (cases \<Sigma>') auto
  next case 7
    thus ?case by (cases \<Sigma>') auto
  next case 8
    thus ?case by (cases \<Sigma>') auto
  next case 9
    thus ?case by (cases \<Sigma>') auto
  next case 10
    thus ?case by (cases \<Sigma>') auto
  next case 11
    thus ?case by (cases \<Sigma>') auto
  qed simp_all

theorem flattening_correct [simp]: "iterate (eval_stack \<Pi>) \<Sigma> \<Sigma>' \<Longrightarrow>
    iterate (eval_flat_stack (flatten \<Pi>)) (state_convert \<Sigma>) (state_convert \<Sigma>')"
  by (induction "eval_stack \<Pi>" \<Sigma> \<Sigma>' rule: iterate.induct) simp_all

end