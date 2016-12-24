theory Flattening
imports StackLanguage "../FlatStack/FlatStackLanguage"
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

definition flatten :: "stack_program \<Rightarrow> flat_stack_program" where
  "flatten \<Pi> = (\<lambda>s. case s of 
      CL\<^sub>2 f s \<Rightarrow> (case \<Pi> f of 
          Some (a, ls, \<Phi>) \<Rightarrow> (case \<Phi> s of
              Some (\<pi>, s') \<Rightarrow> Some (instruction_convert f 0 ls \<pi>, CL\<^sub>2 f s')
            | None \<Rightarrow> None)
        | None \<Rightarrow> None))"

definition flatten_frame :: "frame \<Rightarrow> int list" where
  "flatten_frame f = 
    map stack_value_convert (frame.arguments f @ frame.locals f @ frame.saved_stack f)"

fun state_convert :: "stack_state \<Rightarrow> flat_stack_state" where
  "state_convert (\<sigma>, \<phi>, \<pi>, s, \<omega>) = (
    let fr = hd \<phi> 
    in let f = frame.name fr
    in (map stack_value_convert \<sigma> @ concat (map flatten_frame \<phi>), 
        instruction_convert f (length \<sigma>) (length (frame.locals fr)) \<pi>, CL\<^sub>2 f s, \<omega>))"

(* flattening correct *)

lemma [simp]: "flat_stack_output (state_convert \<Sigma>\<^sub>S) = stack_output \<Sigma>\<^sub>S"
  proof (induction \<Sigma>\<^sub>S rule: state_convert.induct) 
  case (1 \<sigma> \<phi> \<pi> s \<omega>)
    thus ?case by (cases "hd \<phi>") simp
  qed

lemma [simp]: "finite (dom \<Pi>) \<Longrightarrow> finite (dom (flatten \<Pi>))"
  apply simp
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

lemma [simp]: "\<Pi> f = Some (a, l, \<Phi>) \<Longrightarrow> \<Phi> s = Some (\<pi>, s') \<Longrightarrow> 
    flatten \<Pi> (CL\<^sub>2 f s) = Some (instruction_convert f 0 l \<pi>, CL\<^sub>2 f s')"
  by simp

lemma [simp]: "eval_stack \<Pi> \<Sigma> \<Sigma>' \<Longrightarrow> valid_state \<Pi> \<Sigma> \<Longrightarrow>
    eval_flat_stack (flatten \<Pi>) (state_convert \<Sigma>) (state_convert \<Sigma>')"
  proof (induction \<Pi> \<Sigma> \<Sigma>' rule: eval_stack.induct)
  case (evs_jump \<Pi> f a l \<Phi> s \<pi> s' \<phi> \<omega>)
    from evs_jump have "\<Pi> (frame.name f) = Some (a, l, \<Phi>)" by simp
    from evs_jump have "\<Phi> s = Some (\<pi>, s')" by simp
    from evs_jump have "valid_frame \<Pi> f" by simp
    from evs_jump have "\<forall>fr \<in> set \<phi>. valid_frame \<Pi> fr" by simp


have "flatten \<Pi> ss = Some (s\<pi>, ss') \<Longrightarrow> eval_flat_stack (flatten \<Pi>) (\<sigma>, [], ss, \<omega>) (\<sigma>, s\<pi>, ss', \<omega>)" by simp

    have "eval_flat_stack (flatten \<Pi>) 
     (flatten_frame f @ concat (map flatten_frame \<phi>), [], CL\<^sub>2 (name f) s, \<omega>)
     (flatten_frame f @ concat (map flatten_frame \<phi>), instruction_convert (name f) 0 (length (locals f)) \<pi>, CL\<^sub>2 (name f) s', \<omega>)" by simp
    thus ?case by (simp add: Let_def)
  next case (evs_push_l)
    thus ?case by (simp add: Let_def)
  next case (evs_push_a)
    thus ?case by (simp add: Let_def)
  next case (evs_pop_l)
    thus ?case by (simp add: Let_def)
  next case (evs_pop_a) 
    thus ?case by (simp add: Let_def)
  next case (evs_if_t)
    thus ?case by (simp add: Let_def)
  next case (evs_if_f)
    thus ?case by (simp add: Let_def)
  next case (evs_goto \<Pi> f a l \<Phi> s \<pi> s' \<phi> \<pi>' s'' \<omega>)
    hence "valid_frame \<Pi> f" by simp
    with evs_goto show ?case by (simp_all add: Let_def)
  next case (evs_call)
    thus ?case by (simp add: Let_def)
  next case (evs_return)
    thus ?case by (simp add: Let_def)
  qed (simp_all add: Let_def)

theorem flattening_correct [simp]: "iterate_ind (eval_stack \<Pi>) \<Sigma> \<Sigma>' \<Longrightarrow> valid_state \<Pi> \<Sigma> \<Longrightarrow>
    iterate_ind (eval_flat_stack (flatten \<Pi>)) (state_convert \<Sigma>) (state_convert \<Sigma>')"
  by (induction "eval_stack \<Pi>" \<Sigma> \<Sigma>' rule: iterate_ind.induct) simp_all

end