theory StackToAssembly
imports FlatStackLanguage StackFlattener 
  "../BranchingAssembly/BranchingAssemblyLanguage" "../Utilities/Iterate"
begin

definition pop_to_D :: "computation \<Rightarrow> b_assembly list" where
  "pop_to_D cmp = [CBAssm {A} (Reg M), CBAssm {D} cmp, ABAssm 0, CBAssm {M} (Decr M)]"

definition frame_to_D :: "nat \<Rightarrow> b_assembly list" where
  "frame_to_D n = 
    [CBAssm {D} (Reg M), ABAssm (int n), CBAssm {A} DMinusA, CBAssm {D} (Reg M), ABAssm 0]"

definition push_from_D :: "b_assembly list" where
  "push_from_D = [CBAssm {A, M} (Incr M), CBAssm {M} (Reg D), ABAssm 0]"

(* VERY VERY VERY BAD! Figure out a way to fix this! *)
definition decrA :: "nat \<Rightarrow> b_assembly list" where
  "decrA n = repeat (CBAssm {A} (Decr A)) n"

definition D_to_frame :: "nat \<Rightarrow> b_assembly list" where
  "D_to_frame n = [CBAssm {A} (Reg M)] @ decrA n @ [CBAssm {M} (Reg D), ABAssm 0]"

definition boolify_D :: "comparison \<Rightarrow> b_assembly list" where
  "boolify_D jmp = [IBAssm {jmp} [ABAssm 0, CBAssm {D} One] [ABAssm 0, CBAssm {D} Zero]]"

primrec instruction_conv :: "flat_stack_instruction \<Rightarrow> b_assembly list" where
  "instruction_conv FAdd = pop_to_D (Reg M) @ pop_to_D DPlusM @ push_from_D"
| "instruction_conv FSub = pop_to_D (Reg M) @ pop_to_D MMinusD @ push_from_D"
| "instruction_conv FNeg = pop_to_D (NegR M) @ push_from_D"
| "instruction_conv FEq = pop_to_D (Reg M) @ pop_to_D MMinusD @ boolify_D EQ @ push_from_D"
| "instruction_conv FGt = pop_to_D (Reg M) @ pop_to_D MMinusD @ boolify_D GT @ push_from_D"
| "instruction_conv FLt = pop_to_D (Reg M) @ pop_to_D MMinusD @ boolify_D LT @ push_from_D"
| "instruction_conv FAnd = pop_to_D (Reg M) @ pop_to_D DAndM @ push_from_D"
| "instruction_conv FOr = pop_to_D (Reg M) @ pop_to_D DOrM @ push_from_D"
| "instruction_conv FNot = pop_to_D (NotR M) @ push_from_D"
| "instruction_conv (FCon i) = [ABAssm i, CBAssm {D} (Reg A), ABAssm 0] @ push_from_D"
| "instruction_conv (FDup n) = frame_to_D n @ push_from_D"
| "instruction_conv (FUpd n) = pop_to_D (Reg M) @ D_to_frame n"
| "instruction_conv (FIf \<pi>\<^sub>t \<pi>\<^sub>f) = pop_to_D (Reg M) @ 
    [IBAssm {GT, LT} (ABAssm 0 # concat (map instruction_conv \<pi>\<^sub>t)) 
                 (ABAssm 0 # concat (map instruction_conv \<pi>\<^sub>f))]" 
      (* {GT, LT} here represents boolification *)
| "instruction_conv (FGoto s) = [JBAssm s]"
| "instruction_conv FPrint = pop_to_D (Reg M) @ [PBAssm]"

definition program_convert :: "flat_stack_program \<Rightarrow> b_assembly_program" where
  "program_convert \<Pi> = map_option (\<lambda>(\<pi>, s). (ABAssm 0 # concat (map instruction_conv \<pi>), s)) o \<Pi>"

fun state_convert :: "flat_stack_state \<Rightarrow> b_assembly_state set" where
  "state_convert (\<sigma>, \<pi>, s, \<omega>) = 
    {(stack_to_mem \<sigma> \<mu>, Some 0, d, concat (map instruction_conv \<pi>), s, \<omega>) | d \<mu>. True }"

(* conversion correctness *)

lemma [simp]: "\<Sigma>\<^sub>B \<in> state_convert \<Sigma>\<^sub>S \<Longrightarrow> b_assembly_output \<Sigma>\<^sub>B = flat_stack_output \<Sigma>\<^sub>S"
  by (induction \<Sigma>\<^sub>S rule: flat_stack_output.induct, induction \<Sigma>\<^sub>B rule: b_assembly_output.induct) simp

lemma [simp]: "dom (program_convert \<Pi>) = dom \<Pi>"
  by (auto simp add: program_convert_def)

lemma [simp]: "\<Pi> s = Some (\<pi>, s') \<Longrightarrow> 
    program_convert \<Pi> s = Some (ABAssm 0 # concat (map instruction_conv \<pi>), s')"
  by (simp add: program_convert_def)

lemma eval_pop_to_D: "iterate (eval_b_assembly \<Pi>) 
    (stack_to_mem (i1 # \<sigma>) \<mu>, Some 0, d, pop_to_D cmp @ \<pi>, s, \<omega>) 
    (stack_to_mem \<sigma> (stack_to_mem (i1 # \<sigma>) \<mu>), Some 0, compute cmp i1 (1 + int (length \<sigma>)) d, \<pi>, s, \<omega>)"
  proof (unfold pop_to_D_def)
    let ?\<mu> = "stack_to_mem (i1 # \<sigma>) \<mu>"
    let ?\<Sigma>\<^sub>0 = "(?\<mu>, Some 0, d, 
      [CBAssm {A} (Reg M), CBAssm {D} cmp, ABAssm 0, CBAssm {M} (Decr M)] @ \<pi>, s, \<omega>)"
    let ?\<Sigma>\<^sub>1 = "(?\<mu>, Some (?\<mu> 0), d, [CBAssm {D} cmp, ABAssm 0, CBAssm {M} (Decr M)] @ \<pi>, s, \<omega>)"
    let ?\<Sigma>\<^sub>2 = "(?\<mu>, Some (?\<mu> 0), compute cmp i1 (1 + int (length \<sigma>)) d, 
      [ABAssm 0, CBAssm {M} (Decr M)] @ \<pi>, s, \<omega>)"
    let ?\<Sigma>\<^sub>3 = "(?\<mu>, Some 0, compute cmp i1 (1 + int (length \<sigma>)) d, [CBAssm {M} (Decr M)] @ \<pi>, s, \<omega>)"
    let ?\<Sigma>\<^sub>4 = "(stack_to_mem \<sigma> ?\<mu>, Some 0, compute cmp i1 (1 + int (length \<sigma>)) d, \<pi>, s, \<omega>)"
    have step1: "eval_b_assembly \<Pi> ?\<Sigma>\<^sub>0 = Some ?\<Sigma>\<^sub>1" by simp
    have "eval_b_assembly \<Pi> ?\<Sigma>\<^sub>1 = Some ?\<Sigma>\<^sub>2" by auto
    with step1 iter_two have step12: "iterate (eval_b_assembly \<Pi>) ?\<Sigma>\<^sub>0 ?\<Sigma>\<^sub>2" by fast
    have step3: "eval_b_assembly \<Pi> ?\<Sigma>\<^sub>2 = Some ?\<Sigma>\<^sub>3" by simp
    have "eval_b_assembly \<Pi> ?\<Sigma>\<^sub>3 = Some ?\<Sigma>\<^sub>4" by simp
    with step3 iter_two have "iterate (eval_b_assembly \<Pi>) ?\<Sigma>\<^sub>2 ?\<Sigma>\<^sub>4" by fast
    with step12 show "iterate (eval_b_assembly \<Pi>) ?\<Sigma>\<^sub>0 ?\<Sigma>\<^sub>4" by fast
  qed

lemma eval_frame_to_D: "n < length \<sigma> \<Longrightarrow> iterate (eval_b_assembly \<Pi>) 
    (stack_to_mem \<sigma> \<mu>, Some 0, d, frame_to_D n @ \<pi>, s, \<omega>)
    (stack_to_mem \<sigma> \<mu>, Some 0, \<sigma> ! n, \<pi>, s, \<omega>)"
  proof (unfold frame_to_D_def)
    let ?\<Sigma>\<^sub>0 = "(stack_to_mem \<sigma> \<mu>, Some 0, d, [CBAssm {D} (Reg M), ABAssm (int n), CBAssm {A} DMinusA, 
      CBAssm {D} (Reg M), ABAssm 0] @ \<pi>, s, \<omega>)"
    let ?\<Sigma>\<^sub>1 = "(stack_to_mem \<sigma> \<mu>, Some 0, int (length \<sigma>), 
      [ABAssm (int n), CBAssm {A} DMinusA, CBAssm {D} (Reg M), ABAssm 0] @ \<pi>, s, \<omega>)"
    let ?\<Sigma>\<^sub>2 = "(stack_to_mem \<sigma> \<mu>, Some (int n), int (length \<sigma>), 
      [CBAssm {A} DMinusA, CBAssm {D} (Reg M), ABAssm 0] @ \<pi>, s, \<omega>)"
    let ?\<Sigma>\<^sub>3 = "(stack_to_mem \<sigma> \<mu>, Some (int (length \<sigma>) - int n), int (length \<sigma>), 
      [CBAssm {D} (Reg M), ABAssm 0] @ \<pi>, s, \<omega>)"
    let ?\<Sigma>\<^sub>4 = "(stack_to_mem \<sigma> \<mu>, Some (int (length \<sigma>) - int n), \<sigma> ! n, [ABAssm 0] @ \<pi>, s, \<omega>)"
    let ?\<Sigma>\<^sub>5 = "(stack_to_mem \<sigma> \<mu>, Some 0, \<sigma> ! n, \<pi>, s, \<omega>)"
    have step1: "eval_b_assembly \<Pi> ?\<Sigma>\<^sub>0 = Some ?\<Sigma>\<^sub>1" by simp
    have "eval_b_assembly \<Pi> ?\<Sigma>\<^sub>1 = Some ?\<Sigma>\<^sub>2" by simp
    with step1 iter_two have step12: "iterate (eval_b_assembly \<Pi>) ?\<Sigma>\<^sub>0 ?\<Sigma>\<^sub>2" by fast
    have step3: "eval_b_assembly \<Pi> ?\<Sigma>\<^sub>2 = Some ?\<Sigma>\<^sub>3" by simp
    assume "n < length \<sigma>"
    hence "eval_b_assembly \<Pi> ?\<Sigma>\<^sub>3 = Some ?\<Sigma>\<^sub>4" by simp
    with step3 iter_two have step34: "iterate (eval_b_assembly \<Pi>) ?\<Sigma>\<^sub>2 ?\<Sigma>\<^sub>4" by fast
    have "eval_b_assembly \<Pi> ?\<Sigma>\<^sub>4 = Some ?\<Sigma>\<^sub>5" by simp
    with step12 step34 iter_one show "iterate (eval_b_assembly \<Pi>) ?\<Sigma>\<^sub>0 ?\<Sigma>\<^sub>5" by fast
  qed

lemma eval_push_from_D: "iterate (eval_b_assembly \<Pi>) 
    (stack_to_mem \<sigma> \<mu>, Some 0, d, push_from_D @ \<pi>, s, \<omega>) 
    (stack_to_mem (d # \<sigma>) \<mu>, Some 0, d, \<pi>, s, \<omega>)"
  proof (unfold push_from_D_def)
    let ?\<Sigma>\<^sub>0 = "(stack_to_mem \<sigma> \<mu>, Some 0, d, 
      [CBAssm {A, M} (Incr M), CBAssm {M} (Reg D), ABAssm 0] @ \<pi>, s, \<omega>)"
    let ?\<Sigma>\<^sub>1 = "((stack_to_mem \<sigma> \<mu>)(0 := int (length \<sigma>) + 1), Some (int (length \<sigma>) + 1), d, 
      [CBAssm {M} (Reg D), ABAssm 0] @ \<pi>, s, \<omega>)"
    let ?\<Sigma>\<^sub>2 = "(stack_to_mem (d # \<sigma>) \<mu>, Some (int (length \<sigma>) + 1), d, [ABAssm 0] @ \<pi>, s, \<omega>)"
    let ?\<Sigma>\<^sub>3 = "(stack_to_mem (d # \<sigma>) \<mu>, Some 0, d, \<pi>, s, \<omega>)"
    have step1: "eval_b_assembly \<Pi> ?\<Sigma>\<^sub>0 = Some ?\<Sigma>\<^sub>1" by (simp add: Let_def)
    have step2: "eval_b_assembly \<Pi> ?\<Sigma>\<^sub>1 = Some ?\<Sigma>\<^sub>2" by simp
    have "eval_b_assembly \<Pi> ?\<Sigma>\<^sub>2 = Some ?\<Sigma>\<^sub>3" by simp
    with step1 step2 iter_two iter_prestep show "iterate (eval_b_assembly \<Pi>) ?\<Sigma>\<^sub>0 ?\<Sigma>\<^sub>3" by fast
  qed

lemma eval_decrA: "iterate (eval_b_assembly \<Pi>) 
    (\<mu>, Some a, d, decrA n @ \<pi>, s, \<omega>) 
    (\<mu>, Some (a - int n), d, \<pi>, s, \<omega>)"
  proof (induction n arbitrary: a)
  case 0
    thus ?case by (simp add: decrA_def)
  next case (Suc n)
    let ?\<Sigma>\<^sub>0 = "(\<mu>, Some a, d, CBAssm {A} (Decr A) # decrA n @ \<pi>, s, \<omega>)"
    let ?\<Sigma>\<^sub>1 = "(\<mu>, Some (a - 1), d, decrA n @ \<pi>, s, \<omega>)"
    let ?\<Sigma>\<^sub>2' = "(\<mu>, Some ((a - 1) - int n), d, \<pi>, s, \<omega>)"
    let ?\<Sigma>\<^sub>2 = "(\<mu>, Some (a - int (Suc n)), d, \<pi>, s, \<omega>)"
    have step1: "eval_b_assembly \<Pi> ?\<Sigma>\<^sub>0 = Some ?\<Sigma>\<^sub>1" by simp
    from Suc have "iterate (eval_b_assembly \<Pi>) ?\<Sigma>\<^sub>1 ?\<Sigma>\<^sub>2'" by simp
    moreover have "?\<Sigma>\<^sub>2' = ?\<Sigma>\<^sub>2" by simp
    ultimately have "iterate (eval_b_assembly \<Pi>) ?\<Sigma>\<^sub>1 ?\<Sigma>\<^sub>2" by simp
    with step1 iter_one have "iterate (eval_b_assembly \<Pi>) ?\<Sigma>\<^sub>0 ?\<Sigma>\<^sub>2" by fast
    thus ?case by (simp add: decrA_def)
  qed

lemma eval_D_to_frame: "n < length \<sigma> \<Longrightarrow> iterate (eval_b_assembly \<Pi>) 
    (stack_to_mem \<sigma> \<mu>, Some 0, d, D_to_frame n @ \<pi>, s, \<omega>)
    (stack_to_mem (\<sigma>[n := d]) \<mu>, Some 0, d, \<pi>, s, \<omega>)"
  proof (unfold D_to_frame_def)
    let ?\<Sigma>\<^sub>0 = "(stack_to_mem \<sigma> \<mu>, Some 0, d, 
      ([CBAssm {A} (Reg M)] @ decrA n @ [CBAssm {M} (Reg D), ABAssm 0]) @ \<pi>, s, \<omega>)"
    let ?\<Sigma>\<^sub>1 = "(stack_to_mem \<sigma> \<mu>, Some (int (length \<sigma>)), d, 
      decrA n @ [CBAssm {M} (Reg D), ABAssm 0] @ \<pi>, s, \<omega>)"
    let ?\<Sigma>\<^sub>2 = "(stack_to_mem \<sigma> \<mu>, Some (int (length \<sigma>) - int n), d, 
      [CBAssm {M} (Reg D), ABAssm 0] @ \<pi>, s, \<omega>)"
    let ?\<Sigma>\<^sub>3 = "(stack_to_mem (\<sigma>[n := d]) \<mu>, Some (int (length \<sigma>) - int n), d, 
      [ABAssm 0] @ \<pi>, s, \<omega>)"
    let ?\<Sigma>\<^sub>4 = "(stack_to_mem (\<sigma>[n := d]) \<mu>, Some 0, d, \<pi>, s, \<omega>)"
    have step1: "eval_b_assembly \<Pi> ?\<Sigma>\<^sub>0 = Some ?\<Sigma>\<^sub>1" by simp
    from eval_decrA have "iterate (eval_b_assembly \<Pi>) ?\<Sigma>\<^sub>1 ?\<Sigma>\<^sub>2" by simp
    with step1 iter_one have step12: "iterate (eval_b_assembly \<Pi>) ?\<Sigma>\<^sub>0 ?\<Sigma>\<^sub>2" by fast
    assume "n < length \<sigma>"
    hence step3: "eval_b_assembly \<Pi> ?\<Sigma>\<^sub>2 = Some ?\<Sigma>\<^sub>3" by simp
    have "eval_b_assembly \<Pi> ?\<Sigma>\<^sub>3 = Some ?\<Sigma>\<^sub>4" by simp
    with step3 iter_two have step34: "iterate (eval_b_assembly \<Pi>) ?\<Sigma>\<^sub>2 ?\<Sigma>\<^sub>4" by fast
    with step12 step34 show "iterate (eval_b_assembly \<Pi>) ?\<Sigma>\<^sub>0 ?\<Sigma>\<^sub>4" by fast
  qed

lemma eval_boolify_D: "iterate (eval_b_assembly \<Pi>) 
    (\<sigma>, Some 0, d, boolify_D jmp @ \<pi>, s, \<omega>) 
    (\<sigma>, Some 0, unboolify (compare d {jmp}), \<pi>, s, \<omega>)"
  proof (unfold boolify_D_def)
    let ?\<Sigma>\<^sub>0 = "(\<sigma>, Some 0, d, 
      [IBAssm {jmp} [ABAssm 0, CBAssm {D} One] [ABAssm 0, CBAssm {D} Zero]] @ \<pi>, s, \<omega>)"
    let ?\<Sigma>\<^sub>1\<^sub>t = "(\<sigma>, None, d, [ABAssm 0, CBAssm {D} One] @ \<pi>, s, \<omega>)"
    let ?\<Sigma>\<^sub>1\<^sub>f = "(\<sigma>, None, d, [ABAssm 0, CBAssm {D} Zero] @ \<pi>, s, \<omega>)"
    let ?\<Sigma>\<^sub>2\<^sub>t = "(\<sigma>, Some 0, d, [CBAssm {D} One] @ \<pi>, s, \<omega>)"
    let ?\<Sigma>\<^sub>2\<^sub>f = "(\<sigma>, Some 0, d, [CBAssm {D} Zero] @ \<pi>, s, \<omega>)"
    let ?\<Sigma>\<^sub>3 = "(\<sigma>, Some 0, unboolify (compare d {jmp}), \<pi>, s, \<omega>)"
    show "iterate (eval_b_assembly \<Pi>) ?\<Sigma>\<^sub>0 ?\<Sigma>\<^sub>3"
      proof (cases "compare d {jmp}")
      case True
        hence step1: "eval_b_assembly \<Pi> ?\<Sigma>\<^sub>0 = Some ?\<Sigma>\<^sub>1\<^sub>t" by simp
        have step2: "eval_b_assembly \<Pi> ?\<Sigma>\<^sub>1\<^sub>t = Some ?\<Sigma>\<^sub>2\<^sub>t" by simp
        from True have "eval_b_assembly \<Pi> ?\<Sigma>\<^sub>2\<^sub>t = Some ?\<Sigma>\<^sub>3" by simp
        with step1 step2 iter_two iter_prestep show ?thesis by fast
      next case False
        hence step1: "eval_b_assembly \<Pi> ?\<Sigma>\<^sub>0 = Some ?\<Sigma>\<^sub>1\<^sub>f" by simp
        have step2: "eval_b_assembly \<Pi> ?\<Sigma>\<^sub>1\<^sub>f = Some ?\<Sigma>\<^sub>2\<^sub>f" by simp
        from False have "eval_b_assembly \<Pi> ?\<Sigma>\<^sub>2\<^sub>f = Some ?\<Sigma>\<^sub>3" by auto
        with step1 step2 iter_two iter_prestep show ?thesis by fast
      qed
  qed

lemma eval_stack_conv [simp]: "eval_flat_stack \<Pi> \<Sigma>\<^sub>S \<Sigma>\<^sub>S' \<Longrightarrow> \<Sigma>\<^sub>A \<in> state_convert \<Sigma>\<^sub>S \<Longrightarrow> 
    \<exists>\<Sigma>\<^sub>A'. \<Sigma>\<^sub>A' \<in> state_convert \<Sigma>\<^sub>S' \<and> iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A \<Sigma>\<^sub>A'"
  proof (induction \<Pi> \<Sigma>\<^sub>S \<Sigma>\<^sub>S' rule: eval_flat_stack.induct)
  case (evf_jump \<Pi> s \<pi> s' \<sigma> \<omega>)
    then obtain d \<mu> where M: "\<Sigma>\<^sub>A = (stack_to_mem \<sigma> \<mu>, Some 0, d, [], s, \<omega>)" by fastforce
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    have X: "(stack_to_mem \<sigma> \<mu>, Some 0, d, ?\<pi>', s', \<omega>) \<in> state_convert (\<sigma>, \<pi>, s', \<omega>)" by auto
    from evf_jump have Y:
      "eval_b_assembly (program_convert \<Pi>) (stack_to_mem \<sigma> \<mu>, Some 0, d, [], s, \<omega>) = 
        Some (stack_to_mem \<sigma> \<mu>, None, d, ABAssm 0 # ?\<pi>', s', \<omega>)" by simp
    from evf_jump have "eval_b_assembly (program_convert \<Pi>) 
      (stack_to_mem \<sigma> \<mu>, None, d, ABAssm 0 # ?\<pi>', s', \<omega>) = 
        Some (stack_to_mem \<sigma> \<mu>, Some 0, d, ?\<pi>', s', \<omega>)" by simp
    with X Y M iter_two show ?case by metis
  next case (evf_add \<Pi> i1 i2 \<sigma> \<pi> s \<omega>)
    then obtain d \<mu> where S: "\<Sigma>\<^sub>A = 
      (stack_to_mem (i1 # i2 # \<sigma>) \<mu>, Some 0, d, 
        pop_to_D (Reg M) @ pop_to_D DPlusM @ push_from_D @ concat (map instruction_conv \<pi>), s, \<omega>)" 
      by fastforce
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    let ?\<mu> = "stack_to_mem (i2 # \<sigma>) (stack_to_mem (i1 # i2 # \<sigma>) \<mu>)"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(?\<mu>, Some 0, i1, pop_to_D DPlusM @ push_from_D @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(stack_to_mem \<sigma> ?\<mu>, Some 0, i1 + i2, push_from_D @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>3 = "(stack_to_mem ((i1 + i2) # \<sigma>) ?\<mu>, Some 0, i1 + i2, ?\<pi>', s, \<omega>)"
    have X: "?\<Sigma>\<^sub>A\<^sub>3 \<in> state_convert ((i1 + i2) # \<sigma>, \<pi>, s, \<omega>)" by auto
    from S eval_pop_to_D have step1: "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>1" 
      by fastforce
    from eval_pop_to_D have step2: "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>1 ?\<Sigma>\<^sub>A\<^sub>2" 
      by fastforce
    from eval_push_from_D have "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>2 ?\<Sigma>\<^sub>A\<^sub>3" by simp
    with step1 step2 iter_one X show ?case by fast
  next case (evf_sub \<Pi> i1 i2 \<sigma> \<pi> s \<omega>)
    then obtain d \<mu> where S: "\<Sigma>\<^sub>A = 
      (stack_to_mem (i1 # i2 # \<sigma>) \<mu>, Some 0, d, 
        pop_to_D (Reg M) @ pop_to_D MMinusD @ push_from_D @ concat (map instruction_conv \<pi>), s, \<omega>)" 
      by fastforce
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    let ?\<mu> = "stack_to_mem (i2 # \<sigma>) (stack_to_mem (i1 # i2 # \<sigma>) \<mu>)"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(?\<mu>, Some 0, i1, pop_to_D MMinusD @ push_from_D @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(stack_to_mem \<sigma> ?\<mu>, Some 0, i2 - i1, push_from_D @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>3 = "(stack_to_mem ((i2 - i1) # \<sigma>) ?\<mu>, Some 0, i2 - i1, ?\<pi>', s, \<omega>)"
    have X: "?\<Sigma>\<^sub>A\<^sub>3 \<in> state_convert ((i2 - i1) # \<sigma>, \<pi>, s, \<omega>)" by auto
    from S eval_pop_to_D have step1: "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>1" 
      by fastforce
    from eval_pop_to_D have step2: "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>1 ?\<Sigma>\<^sub>A\<^sub>2" 
      by fastforce
    from eval_push_from_D have "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>2 ?\<Sigma>\<^sub>A\<^sub>3" by simp
    with step1 step2 iter_one X show ?case by fast
  next case (evf_neg \<Pi> i1 \<sigma> \<pi> s \<omega>)
    then obtain d \<mu> where S: "\<Sigma>\<^sub>A = 
      (stack_to_mem (i1 # \<sigma>) \<mu>, Some 0, d, 
        pop_to_D (NegR M) @ push_from_D @ concat (map instruction_conv \<pi>), s, \<omega>)" by fastforce
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    let ?\<mu> = "stack_to_mem (i1 # \<sigma>) \<mu>"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(stack_to_mem \<sigma> ?\<mu>, Some 0, -i1, push_from_D @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(stack_to_mem (-i1 # \<sigma>) ?\<mu>, Some 0, -i1, ?\<pi>', s, \<omega>)"
    have X: "?\<Sigma>\<^sub>A\<^sub>2 \<in> state_convert (-i1 # \<sigma>, \<pi>, s, \<omega>)" by auto
    from S eval_pop_to_D have step1: "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>1" 
      by fastforce
    from eval_push_from_D have "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>1 ?\<Sigma>\<^sub>A\<^sub>2" by simp
    with step1 X show ?case by fast
  next case (evf_eq \<Pi> i1 i2 \<sigma> \<pi> s \<omega>)
    then obtain d \<mu> where S: "\<Sigma>\<^sub>A = 
      (stack_to_mem (i1 # i2 # \<sigma>) \<mu>, Some 0, d, 
        pop_to_D (Reg M) @ pop_to_D MMinusD @ boolify_D EQ @ push_from_D @
          concat (map instruction_conv \<pi>), s, \<omega>)" by fastforce
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    let ?\<mu> = "stack_to_mem (i2 # \<sigma>) (stack_to_mem (i1 # i2 # \<sigma>) \<mu>)"
    let ?result = "unboolify (i2 = i1)"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(?\<mu>, Some 0, i1, pop_to_D MMinusD @ boolify_D EQ @ push_from_D @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(stack_to_mem \<sigma> ?\<mu>, Some 0, i2 - i1, boolify_D EQ @ push_from_D @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>3 = "(stack_to_mem \<sigma> ?\<mu>, Some 0, ?result, push_from_D @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>4 = "(stack_to_mem (?result # \<sigma>) ?\<mu>, Some 0, ?result, ?\<pi>', s, \<omega>)"
    have X: "?\<Sigma>\<^sub>A\<^sub>4 \<in> state_convert (?result # \<sigma>, \<pi>, s, \<omega>)" by auto
    from S eval_pop_to_D have step1: "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>1" 
      by fastforce
    from eval_pop_to_D have step2: "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>1 ?\<Sigma>\<^sub>A\<^sub>2" 
      by fastforce
    from eval_boolify_D have step3: "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>2 ?\<Sigma>\<^sub>A\<^sub>3" 
      by fastforce
    from eval_push_from_D have "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>3 ?\<Sigma>\<^sub>A\<^sub>4" by simp
    with X step1 step2 step3 iter_one show ?case by fast
  next case (evf_gt \<Pi> i1 i2 \<sigma> \<pi> s \<omega>)
    then obtain d \<mu> where S: "\<Sigma>\<^sub>A = 
      (stack_to_mem (i1 # i2 # \<sigma>) \<mu>, Some 0, d, 
        pop_to_D (Reg M) @ pop_to_D MMinusD @ boolify_D GT @ push_from_D @
          concat (map instruction_conv \<pi>), s, \<omega>)" by fastforce
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    let ?\<mu> = "stack_to_mem (i2 # \<sigma>) (stack_to_mem (i1 # i2 # \<sigma>) \<mu>)"
    let ?result = "unboolify (i2 > i1)"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(?\<mu>, Some 0, i1, 
      pop_to_D MMinusD @ boolify_D GT @ push_from_D @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(stack_to_mem \<sigma> ?\<mu>, Some 0, i2 - i1, boolify_D GT @ push_from_D @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>3' = "(stack_to_mem \<sigma> ?\<mu>, Some 0, unboolify (i2 - i1 > 0), push_from_D @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>3 = "(stack_to_mem \<sigma> ?\<mu>, Some 0, ?result, push_from_D @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>4 = "(stack_to_mem (?result # \<sigma>) ?\<mu>, Some 0, ?result, ?\<pi>', s, \<omega>)"
    have X: "?\<Sigma>\<^sub>A\<^sub>4 \<in> state_convert (?result # \<sigma>, \<pi>, s, \<omega>)" by auto
    from S eval_pop_to_D have step1: "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>1" 
      by fastforce
    from eval_pop_to_D have step2: "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>1 ?\<Sigma>\<^sub>A\<^sub>2" 
      by fastforce
    from eval_boolify_D have "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>2 ?\<Sigma>\<^sub>A\<^sub>3'" 
      by fastforce
    moreover have "?\<Sigma>\<^sub>A\<^sub>3' = ?\<Sigma>\<^sub>A\<^sub>3" by smt
    ultimately have step3: "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>2 ?\<Sigma>\<^sub>A\<^sub>3" by simp
    from eval_push_from_D have "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>3 ?\<Sigma>\<^sub>A\<^sub>4" by simp
    with X step1 step2 step3 iter_one show ?case by fast
  next case (evf_lt \<Pi> i1 i2 \<sigma> \<pi> s \<omega>)
    then obtain d \<mu> where S: "\<Sigma>\<^sub>A = 
      (stack_to_mem (i1 # i2 # \<sigma>) \<mu>, Some 0, d, 
        pop_to_D (Reg M) @ pop_to_D MMinusD @ boolify_D LT @ push_from_D @
          concat (map instruction_conv \<pi>), s, \<omega>)" by fastforce
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    let ?\<mu> = "stack_to_mem (i2 # \<sigma>) (stack_to_mem (i1 # i2 # \<sigma>) \<mu>)"
    let ?result = "unboolify (i2 < i1)"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(?\<mu>, Some 0, i1, 
      pop_to_D MMinusD @ boolify_D LT @ push_from_D @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(stack_to_mem \<sigma> ?\<mu>, Some 0, i2 - i1, boolify_D LT @ push_from_D @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>3 = "(stack_to_mem \<sigma> ?\<mu>, Some 0, ?result, push_from_D @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>4 = "(stack_to_mem (?result # \<sigma>) ?\<mu>, Some 0, ?result, ?\<pi>', s, \<omega>)"
    have X: "?\<Sigma>\<^sub>A\<^sub>4 \<in> state_convert (?result # \<sigma>, \<pi>, s, \<omega>)" by auto
    from S eval_pop_to_D have step1: "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>1" 
      by fastforce
    from eval_pop_to_D have step2: "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>1 ?\<Sigma>\<^sub>A\<^sub>2" 
      by fastforce
    from eval_boolify_D have step3: "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>2 ?\<Sigma>\<^sub>A\<^sub>3" 
      by fastforce
    from eval_push_from_D have "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>3 ?\<Sigma>\<^sub>A\<^sub>4" by simp
    with X step1 step2 step3 iter_one show ?case by fast
  next case (evf_and \<Pi> i1 i2 \<sigma> \<pi> s \<omega>)
    then obtain d \<mu> where S: "\<Sigma>\<^sub>A = 
      (stack_to_mem (i1 # i2 # \<sigma>) \<mu>, Some 0, d, 
        pop_to_D (Reg M) @ pop_to_D DAndM @ push_from_D @ concat (map instruction_conv \<pi>), s, \<omega>)" 
      by fastforce
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    let ?\<mu> = "stack_to_mem (i2 # \<sigma>) (stack_to_mem (i1 # i2 # \<sigma>) \<mu>)"
    let ?result = "unboolify (boolify i1 \<and> boolify i2)"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(?\<mu>, Some 0, i1, pop_to_D DAndM @ push_from_D @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(stack_to_mem \<sigma> ?\<mu>, Some 0, ?result, push_from_D @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>3 = "(stack_to_mem (?result # \<sigma>) ?\<mu>, Some 0, ?result, ?\<pi>', s, \<omega>)"
    have X: "?\<Sigma>\<^sub>A\<^sub>3 \<in> state_convert (?result # \<sigma>, \<pi>, s, \<omega>)" by auto
    from S eval_pop_to_D have step1: "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>1" 
      by fastforce
    from eval_pop_to_D have step2: "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>1 ?\<Sigma>\<^sub>A\<^sub>2" 
      by fastforce
    from eval_push_from_D have "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>2 ?\<Sigma>\<^sub>A\<^sub>3" by simp
    with step1 step2 iter_one X show ?case by fast
  next case (evf_or \<Pi> i1 i2 \<sigma> \<pi> s \<omega>)
    then obtain d \<mu> where S: "\<Sigma>\<^sub>A = 
      (stack_to_mem (i1 # i2 # \<sigma>) \<mu>, Some 0, d, 
        pop_to_D (Reg M) @ pop_to_D DOrM @ push_from_D @ concat (map instruction_conv \<pi>), s, \<omega>)" 
      by fastforce
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    let ?\<mu> = "stack_to_mem (i2 # \<sigma>) (stack_to_mem (i1 # i2 # \<sigma>) \<mu>)"
    let ?result = "unboolify (boolify i1 \<or> boolify i2)"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(?\<mu>, Some 0, i1, pop_to_D DOrM @ push_from_D @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(stack_to_mem \<sigma> ?\<mu>, Some 0, ?result, push_from_D @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>3 = "(stack_to_mem (?result # \<sigma>) ?\<mu>, Some 0, ?result, ?\<pi>', s, \<omega>)"
    have X: "?\<Sigma>\<^sub>A\<^sub>3 \<in> state_convert (?result # \<sigma>, \<pi>, s, \<omega>)" by auto
    from S eval_pop_to_D have step1: "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>1" 
      by fastforce
    from eval_pop_to_D have step2: "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>1 ?\<Sigma>\<^sub>A\<^sub>2" 
      by fastforce
    from eval_push_from_D have "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>2 ?\<Sigma>\<^sub>A\<^sub>3" by simp
    with step1 step2 iter_one X show ?case by fast
  next case (evf_not \<Pi> i1 \<sigma> \<pi> s \<omega>)
    then obtain d \<mu> where S: "\<Sigma>\<^sub>A = 
      (stack_to_mem (i1 # \<sigma>) \<mu>, Some 0, d, 
        pop_to_D (NotR M) @ push_from_D @ concat (map instruction_conv \<pi>), s, \<omega>)" by fastforce
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    let ?\<mu> = "stack_to_mem (i1 # \<sigma>) \<mu>"
    let ?result = "unboolify (\<not> boolify i1)"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(stack_to_mem \<sigma> ?\<mu>, Some 0, ?result, push_from_D @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(stack_to_mem (?result # \<sigma>) ?\<mu>, Some 0, ?result, ?\<pi>', s, \<omega>)"
    have X: "?\<Sigma>\<^sub>A\<^sub>2 \<in> state_convert (?result # \<sigma>, \<pi>, s, \<omega>)" by auto
    from S eval_pop_to_D have step1: "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>1" 
      by fastforce
    from eval_push_from_D have "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>1 ?\<Sigma>\<^sub>A\<^sub>2" by simp
    with step1 X show ?case by fast
  next case (evf_con \<Pi> \<sigma> i \<pi> s \<omega>)
    then obtain d \<mu> where S: "\<Sigma>\<^sub>A = 
      (stack_to_mem \<sigma> \<mu>, Some 0, d, 
        [ABAssm i, CBAssm {D} (Reg A), ABAssm 0] @ push_from_D @ 
          concat (map instruction_conv \<pi>), s, \<omega>)" by fastforce
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    let ?\<mu> = "stack_to_mem \<sigma> \<mu>"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(?\<mu>, Some i, d, [CBAssm {D} (Reg A), ABAssm 0] @ push_from_D @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(?\<mu>, Some i, i, [ABAssm 0] @ push_from_D @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>3 = "(?\<mu>, Some 0, i, push_from_D @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>4 = "(stack_to_mem (i # \<sigma>) \<mu>, Some 0, i, ?\<pi>', s, \<omega>)"
    have X: "?\<Sigma>\<^sub>A\<^sub>4 \<in> state_convert (i # \<sigma>, \<pi>, s, \<omega>)" by auto
    from S have step1: "eval_b_assembly (program_convert \<Pi>) \<Sigma>\<^sub>A = Some ?\<Sigma>\<^sub>A\<^sub>1" by simp
    have "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>1 = Some ?\<Sigma>\<^sub>A\<^sub>2" by simp
    with step1 iter_two have step12: "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>2" by fast
    have step3: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>2 = Some ?\<Sigma>\<^sub>A\<^sub>3" by simp
    from eval_push_from_D have "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>3 ?\<Sigma>\<^sub>A\<^sub>4" by simp
    with step12 step3 iter_one X show ?case by fast
  next case (evf_dup n \<sigma> \<Pi> \<pi> s \<omega>)
    then obtain d \<mu> where S: "\<Sigma>\<^sub>A = 
      (stack_to_mem \<sigma> \<mu>, Some 0, d, 
        frame_to_D n @ push_from_D @ concat (map instruction_conv \<pi>), s, \<omega>)" 
      by fastforce
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    let ?result = "\<sigma> ! n"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(stack_to_mem \<sigma> \<mu>, Some 0, ?result, push_from_D @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(stack_to_mem (?result # \<sigma>) \<mu>, Some 0, ?result, ?\<pi>', s, \<omega>)"
    have X: "?\<Sigma>\<^sub>A\<^sub>2 \<in> state_convert (?result # \<sigma>, \<pi>, s, \<omega>)" by auto
    from S evf_dup eval_frame_to_D have step1: 
      "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>1" by metis
    from eval_push_from_D have "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>1 ?\<Sigma>\<^sub>A\<^sub>2" by simp
    with step1 X show ?case by fast
  next case (evf_upd n \<sigma> \<Pi> i1 \<pi> s \<omega>)
    then obtain d \<mu> where S: "\<Sigma>\<^sub>A = 
      (stack_to_mem (i1 # \<sigma>) \<mu>, Some 0, d, 
        pop_to_D (Reg M) @ D_to_frame n @ concat (map instruction_conv \<pi>), s, \<omega>)" 
      by fastforce
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    let ?\<mu> = "stack_to_mem (i1 # \<sigma>) \<mu>"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(stack_to_mem \<sigma> ?\<mu>, Some 0, i1, D_to_frame n @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(stack_to_mem (\<sigma>[n := i1]) ?\<mu>, Some 0, i1, ?\<pi>', s, \<omega>)"
    have X: "?\<Sigma>\<^sub>A\<^sub>2 \<in> state_convert (\<sigma>[n := i1], \<pi>, s, \<omega>)" by auto
    from S eval_pop_to_D have step1: "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>1" 
      by fastforce
    from evf_upd eval_D_to_frame have "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>1 ?\<Sigma>\<^sub>A\<^sub>2" 
      by simp
    with step1 X show ?case by fast
  next case (evs_if_t i1 \<Pi> \<sigma> \<pi>\<^sub>t \<pi>\<^sub>f \<pi> s \<omega>)
    let ?\<pi>\<^sub>A = "concat (map instruction_conv \<pi>)"
    let ?\<pi>\<^sub>t\<^sub>A = "concat (map instruction_conv \<pi>\<^sub>t)"
    let ?\<pi>\<^sub>f\<^sub>A = "concat (map instruction_conv \<pi>\<^sub>f)"
    from evs_if_t obtain d \<mu> where S: "\<Sigma>\<^sub>A = 
      (stack_to_mem (i1 # \<sigma>) \<mu>, Some 0, d, 
        pop_to_D (Reg M) @ [IBAssm {GT, LT} (ABAssm 0 # ?\<pi>\<^sub>t\<^sub>A) (ABAssm 0 # ?\<pi>\<^sub>f\<^sub>A)] @ ?\<pi>\<^sub>A, s, \<omega>)" 
      by fastforce
    let ?\<mu> = "stack_to_mem (i1 # \<sigma>) \<mu>"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(stack_to_mem \<sigma> ?\<mu>, Some 0, i1, 
      [IBAssm {GT, LT} (ABAssm 0 # ?\<pi>\<^sub>t\<^sub>A) (ABAssm 0 # ?\<pi>\<^sub>f\<^sub>A)] @ ?\<pi>\<^sub>A, s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(stack_to_mem \<sigma> ?\<mu>, None, i1, ABAssm 0 # ?\<pi>\<^sub>t\<^sub>A @ ?\<pi>\<^sub>A, s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>3 = "(stack_to_mem \<sigma> ?\<mu>, Some 0, i1, ?\<pi>\<^sub>t\<^sub>A @ ?\<pi>\<^sub>A, s, \<omega>)"
    have X: "?\<Sigma>\<^sub>A\<^sub>3 \<in> state_convert (\<sigma>, \<pi>\<^sub>t @ \<pi>, s, \<omega>)" by auto
    from S eval_pop_to_D have step1: "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>1" 
      by fastforce
    from evs_if_t have step2: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>1 = Some ?\<Sigma>\<^sub>A\<^sub>2" 
      by (auto simp add: boolify_def)
    have "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>2 = Some ?\<Sigma>\<^sub>A\<^sub>3" by simp
    with step1 step2 iter_two have "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>3" by fast
    with X S show ?case by fast
  next case (evs_if_f i1 \<Pi> \<sigma> \<pi>\<^sub>t \<pi>\<^sub>f \<pi> s \<omega>)
    let ?\<pi>\<^sub>A = "concat (map instruction_conv \<pi>)"
    let ?\<pi>\<^sub>t\<^sub>A = "concat (map instruction_conv \<pi>\<^sub>t)"
    let ?\<pi>\<^sub>f\<^sub>A = "concat (map instruction_conv \<pi>\<^sub>f)"
    from evs_if_f obtain d \<mu> where S: "\<Sigma>\<^sub>A = 
      (stack_to_mem (i1 # \<sigma>) \<mu>, Some 0, d, 
        pop_to_D (Reg M) @ [IBAssm {GT, LT} (ABAssm 0 # ?\<pi>\<^sub>t\<^sub>A) (ABAssm 0 # ?\<pi>\<^sub>f\<^sub>A)] @ ?\<pi>\<^sub>A, s, \<omega>)" 
      by fastforce
    let ?\<mu> = "stack_to_mem (i1 # \<sigma>) \<mu>"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(stack_to_mem \<sigma> ?\<mu>, Some 0, i1, 
      [IBAssm {GT, LT} (ABAssm 0 # ?\<pi>\<^sub>t\<^sub>A) (ABAssm 0 # ?\<pi>\<^sub>f\<^sub>A)] @ ?\<pi>\<^sub>A, s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(stack_to_mem \<sigma> ?\<mu>, None, i1, ABAssm 0 # ?\<pi>\<^sub>f\<^sub>A @ ?\<pi>\<^sub>A, s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>3 = "(stack_to_mem \<sigma> ?\<mu>, Some 0, i1, ?\<pi>\<^sub>f\<^sub>A @ ?\<pi>\<^sub>A, s, \<omega>)"
    have X: "?\<Sigma>\<^sub>A\<^sub>3 \<in> state_convert (\<sigma>, \<pi>\<^sub>f @ \<pi>, s, \<omega>)" by auto
    from S eval_pop_to_D have step1: "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>1" 
      by fastforce
    from evs_if_f have step2: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>1 = Some ?\<Sigma>\<^sub>A\<^sub>2" 
      by (auto simp add: boolify_def)
    have "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>2 = Some ?\<Sigma>\<^sub>A\<^sub>3" by simp
    with step1 step2 iter_two X show ?case by fast
  next case (evs_goto \<Pi> s \<pi>' s' \<sigma> \<pi> s'' \<omega>)
    then obtain d \<mu> where S: "\<Sigma>\<^sub>A = 
        (stack_to_mem \<sigma> \<mu>, Some 0, d, [JBAssm s] @ concat (map instruction_conv \<pi>), s'', \<omega>)" 
      by fastforce
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(stack_to_mem \<sigma> \<mu>, None, d, ABAssm 0 # concat (map instruction_conv \<pi>'), s', \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(stack_to_mem \<sigma> \<mu>, Some 0, d, concat (map instruction_conv \<pi>'), s', \<omega>)"
    have X: "?\<Sigma>\<^sub>A\<^sub>2 \<in> state_convert (\<sigma>, \<pi>', s', \<omega>)" by auto
    from S evs_goto have step1: "eval_b_assembly (program_convert \<Pi>) \<Sigma>\<^sub>A = Some ?\<Sigma>\<^sub>A\<^sub>1" by simp
    have "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>1 = Some ?\<Sigma>\<^sub>A\<^sub>2" by simp
    with X step1 iter_two show ?case by fast
  next case (evf_print \<Pi> i1 \<sigma> \<pi> s \<omega>)
    then obtain d \<mu> where S: "\<Sigma>\<^sub>A = 
      (stack_to_mem (i1 # \<sigma>) \<mu>, Some 0, d, 
        pop_to_D (Reg M) @ [PBAssm] @ concat (map instruction_conv \<pi>), s, \<omega>)" 
      by fastforce
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    let ?\<mu> = "stack_to_mem (i1 # \<sigma>) \<mu>"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(stack_to_mem \<sigma> ?\<mu>, Some 0, i1, [PBAssm] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(stack_to_mem \<sigma> ?\<mu>, Some 0, i1, ?\<pi>', s, i1 # \<omega>)"
    have X: "?\<Sigma>\<^sub>A\<^sub>2 \<in> state_convert (\<sigma>, \<pi>, s, i1 # \<omega>)" by auto
    from S eval_pop_to_D have step1: "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>1" 
      by fastforce
    have "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>1 = Some ?\<Sigma>\<^sub>A\<^sub>2" by simp
    with step1 X iter_one show ?case by fast
  qed

theorem stack_to_assembly_correct [simp]: "iterate_ind (eval_flat_stack \<Pi>) \<Sigma>\<^sub>S \<Sigma>\<^sub>S' \<Longrightarrow> 
  \<Sigma>\<^sub>B \<in> state_convert \<Sigma>\<^sub>S \<Longrightarrow> 
    \<exists>\<Sigma>\<^sub>B'. \<Sigma>\<^sub>B' \<in> state_convert \<Sigma>\<^sub>S' \<and> iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>B \<Sigma>\<^sub>B'"
  proof (induction "eval_flat_stack \<Pi>" \<Sigma>\<^sub>S \<Sigma>\<^sub>S' arbitrary: \<Sigma>\<^sub>B rule: iterate_ind.induct)
  case iteri_refl
    thus ?case by fastforce
  next case (iteri_step \<Sigma>\<^sub>S \<Sigma>\<^sub>S' \<Sigma>\<^sub>S'')
    then obtain \<Sigma>\<^sub>B' where S: "\<Sigma>\<^sub>B' \<in> state_convert \<Sigma>\<^sub>S' \<and> 
      iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>B \<Sigma>\<^sub>B'" by blast
    with iteri_step eval_stack_conv obtain \<Sigma>\<^sub>B'' where
        "\<Sigma>\<^sub>B'' \<in> state_convert \<Sigma>\<^sub>S'' \<and> iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>B' \<Sigma>\<^sub>B''"
      by blast
    with S have "\<Sigma>\<^sub>B'' \<in> state_convert \<Sigma>\<^sub>S'' \<and> iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>B \<Sigma>\<^sub>B''" 
      by fastforce
    thus ?case by blast
  qed

end