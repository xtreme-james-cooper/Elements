theory Flattening
imports StackLanguage "../FlatStack/FlatStackLanguage" "../Utilities/Iterate"
begin

fun instruction_convert :: "function_name \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> stack_instruction list \<Rightarrow> 
    flat_stack_instruction list" where
  "instruction_convert f ss ls [] = []"
| "instruction_convert f ss ls (Add # \<pi>) = FAdd # instruction_convert f (ss - 1) ls \<pi>"
| "instruction_convert f ss ls (Sub # \<pi>) = FSub # instruction_convert f (ss - 1) ls \<pi>"
| "instruction_convert f ss ls (Neg # \<pi>) = FNeg # instruction_convert f ss ls \<pi>"
| "instruction_convert f ss ls (Eq # \<pi>) = FEq # instruction_convert f (ss - 1) ls \<pi>"
| "instruction_convert f ss ls (Gt # \<pi>) = FGt # instruction_convert f (ss - 1) ls \<pi>"
| "instruction_convert f ss ls (Lt # \<pi>) = FLt # instruction_convert f (ss - 1) ls \<pi>"
| "instruction_convert f ss ls (And # \<pi>) = FAnd # instruction_convert f (ss - 1) ls \<pi>"
| "instruction_convert f ss ls (Or # \<pi>) = FOr # instruction_convert f (ss - 1) ls \<pi>"
| "instruction_convert f ss ls (Not # \<pi>) = FNot # instruction_convert f ss ls \<pi>"
| "instruction_convert f ss ls (Push (Constant i) # \<pi>) = 
    FCon i # instruction_convert f (Suc ss) ls \<pi>"
| "instruction_convert f ss ls (Push (Local v) # \<pi>) = 
    FDup (ss + v) # instruction_convert f (Suc ss) ls \<pi>"
| "instruction_convert f ss ls (Push (Argument v) # \<pi>) = 
    FDup (ss + ls + v) # instruction_convert f (Suc ss) ls \<pi>"
| "instruction_convert f ss ls (Pop (Constant i) # \<pi>) = FUpd 0 # instruction_convert f (ss - 1) ls \<pi>"
| "instruction_convert f ss ls (Pop (Local v) # \<pi>) = 
    FUpd (ss + v) # instruction_convert f (ss - 1) ls \<pi>"
| "instruction_convert f ss ls (Pop (Argument v) # \<pi>) = 
    FUpd (ss + ls + v) # instruction_convert f (ss - 1) ls \<pi>"
| "instruction_convert f ss ls (IfJ \<pi>\<^sub>t \<pi>\<^sub>f # \<pi>) = 
    FIf (instruction_convert f (ss - 1) ls \<pi>\<^sub>t) (instruction_convert f (ss - 1) ls \<pi>\<^sub>f) # 
      instruction_convert f 0 ls \<pi>"
| "instruction_convert f ss ls (Goto s # \<pi>) = [FGoto (CL\<^sub>2 f s)]"
| "instruction_convert f ss ls (Call f' # \<pi>) = undefined # instruction_convert f (ss - 1) ls \<pi>"
| "instruction_convert f ss ls (Return # \<pi>) = undefined # []"
| "instruction_convert f ss ls (Print # \<pi>) = FPrint # instruction_convert f (ss - 1) ls \<pi>"

primrec stack_value_convert :: "stack_value \<Rightarrow> int" where
  "stack_value_convert (IntV i) = i"
| "stack_value_convert (Bool b) = unboolify b"

primrec flatten :: "stack_program \<Rightarrow> flat_stack_program" where
  "flatten \<Pi> (CL\<^sub>2 f s) = (case \<Pi> f of 
      Some (a, ls, \<Phi>) \<Rightarrow> (case \<Phi> s of
          Some (\<pi>, s') \<Rightarrow> Some (instruction_convert f 0 ls \<pi>, CL\<^sub>2 f s')
        | None \<Rightarrow> None)
    | None \<Rightarrow> None)"

primrec flatten_frame :: "frame \<Rightarrow> int list" where
  "flatten_frame (Frame f as ls \<sigma>) = map stack_value_convert (as @ ls @ \<sigma>)"

fun state_convert :: "stack_state \<Rightarrow> flat_stack_state" where
  "state_convert (\<sigma>, \<phi>, \<pi>, s, \<omega>) = (case hd \<phi> of
      Frame f as ls \<sigma> \<Rightarrow> (map stack_value_convert \<sigma> @ concat (map flatten_frame \<phi>), 
        instruction_convert f (length \<sigma>) (length ls) \<pi>, CL\<^sub>2 f s, \<omega>))"

(* flattening correct *)

lemma [simp]: "flat_stack_output (state_convert \<Sigma>\<^sub>S) = stack_output \<Sigma>\<^sub>S"
  proof (induction \<Sigma>\<^sub>S rule: state_convert.induct) 
  case (1 \<sigma> \<phi> \<pi> s \<omega>)
    thus ?case by (cases "hd \<phi>") simp
  qed

lemma [simp]: "finite (dom \<Pi>) \<Longrightarrow> finite (dom (flatten \<Pi>))"
  by simp

lemma [simp]: "eval_flat_stack (flatten \<Pi>) (unboolify b1 # unboolify b2 # \<sigma>, FAnd # \<pi>, s, \<omega>) 
    (unboolify (b2 \<and> b1) # \<sigma>, \<pi>, s, \<omega>)"
  by (cases b1) (cases b2, (metis boolify_def evf_and unboolify_def)+)+

lemma [simp]: "eval_flat_stack (flatten \<Pi>) (unboolify b1 # unboolify b2 # \<sigma>, FOr # \<pi>, s, \<omega>) 
    (unboolify (b2 \<or> b1) # \<sigma>, \<pi>, s, \<omega>)"
  by (cases b1) (cases b2, (metis boolify_def evf_or unboolify_def)+)+

lemma [simp]: "eval_flat_stack (flatten \<Pi>) (unboolify b # \<sigma>, FNot # \<pi>, s, \<omega>) 
    (unboolify (\<not> b) # \<sigma>, \<pi>, s, \<omega>)"
  by (cases b) (metis boolify_def evf_not unboolify_def)+

lemma [simp]: "eval_stack \<Pi> \<Sigma> \<Sigma>' \<Longrightarrow> 
    eval_flat_stack (flatten \<Pi>) (state_convert \<Sigma>) (state_convert \<Sigma>')"
  proof (induction \<Pi> \<Sigma> \<Sigma>' rule: eval_stack.induct)
  case evs_jump
    thus ?case by simp
  next case evs_add
    thus ?case by simp
  next case evs_sub
    thus ?case by simp
  next case evs_neg
    thus ?case by simp
  next case evs_eq
    thus ?case by simp
  next case evs_gt
    thus ?case by simp
  next case evs_lt
    thus ?case by simp
  next case evs_and
    thus ?case by simp
  next case evs_or
    thus ?case by simp
  next case evs_not
    thus ?case by simp
  next case evs_push_c
    thus ?case by simp
  next case evs_goto
    thus ?case by simp
  next case evs_print
    thus ?case by simp
  next case (evs_push_l \<Pi> \<sigma> as ls \<phi> n \<pi> s \<omega>)
    

    have "eval_flat_stack (flatten \<Pi>) (state_convert (\<sigma>, Frame as ls # \<phi>, Push (Local n) # \<pi>, s, \<omega>)) (state_convert (ls ! n # \<sigma>, \<phi>, \<pi>, s, \<omega>))" by simp
    thus ?case by simp
  next case (evs_push_a \<Pi> \<sigma> as ls \<phi> n \<pi> s \<omega>)

    have "eval_flat_stack (flatten \<Pi>) (state_convert (\<sigma>, Frame as ls # \<phi>, Push (Argument n) # \<pi>, s, \<omega>)) (state_convert (as ! n # \<sigma>, \<phi>, \<pi>, s, \<omega>))" by simp
    thus ?case by simp
  next case (evs_pop_l \<Pi> i \<sigma> as ls \<phi> n \<pi> s \<omega>)

    have "eval_flat_stack (flatten \<Pi>) (state_convert (i # \<sigma>, Frame as ls # \<phi>, Pop (Local n) # \<pi>, s, \<omega>)) (state_convert (\<sigma>, Frame as (ls[n := i]) # \<phi>, \<pi>, s, \<omega>))" by simp
    thus ?case by simp
  next case (evs_pop_a \<Pi> i \<sigma> as ls \<phi> n \<pi> s \<omega>) 

    have "eval_flat_stack (flatten \<Pi>) (state_convert (i # \<sigma>, Frame as ls # \<phi>, Pop (Argument n) # \<pi>, s, \<omega>)) (state_convert (\<sigma>, Frame (as[n := i]) ls # \<phi>, \<pi>, s, \<omega>))" by simp
    thus ?case by simp
  next case (evs_if_t \<Pi> \<sigma> \<phi> \<pi>\<^sub>t \<pi>\<^sub>f \<pi> s \<omega>)

    have "eval_flat_stack (flatten \<Pi>) (state_convert (Bool True # \<sigma>, \<phi>, IfJ \<pi>\<^sub>t \<pi>\<^sub>f # \<pi>, s, \<omega>)) (state_convert (\<sigma>, \<phi>, \<pi>\<^sub>t @ \<pi>, s, \<omega>))" by simp
    thus ?case by simp
  next case (evs_if_f \<Pi> \<sigma> \<phi> \<pi>\<^sub>t \<pi>\<^sub>f \<pi> s \<omega>)

    have "eval_flat_stack (flatten \<Pi>) (state_convert (Bool False # \<sigma>, \<phi>, IfJ \<pi>\<^sub>t \<pi>\<^sub>f # \<pi>, s, \<omega>)) (state_convert (\<sigma>, \<phi>, \<pi>\<^sub>f @ \<pi>, s, \<omega>))" by simp
    thus ?case by simp
  next case (evs_call \<Pi> f a l \<Phi> \<sigma> \<phi> \<pi> s \<omega>)

    have "eval_flat_stack (flatten \<Pi>) (state_convert (\<sigma>, \<phi>, Call f # \<pi>, s, \<omega>)) (state_convert ([], Frame f (take a \<sigma>) (repeat (IntV 0) l) (drop a \<sigma>) # \<phi>, \<pi>, s, \<omega>))" by simp
    thus ?case by simp
  next case (evs_return \<Pi> \<sigma> f as ls \<phi> \<pi> s \<omega>)

    have "eval_flat_stack (flatten \<Pi>) (state_convert (\<sigma>, Frame f as ls # \<phi>, Return # \<pi>, s, \<omega>)) (state_convert (\<sigma>, \<phi>, \<pi>, s, \<omega>))" by simp
    thus ?case by simp
  qed

theorem flattening_correct [simp]: "iterate_ind (eval_stack \<Pi>) \<Sigma> \<Sigma>' \<Longrightarrow>
    iterate_ind (eval_flat_stack (flatten \<Pi>)) (state_convert \<Sigma>) (state_convert \<Sigma>')"
  by (induction "eval_stack \<Pi>" \<Sigma> \<Sigma>' rule: iterate_ind.induct) simp_all

end