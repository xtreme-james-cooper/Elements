theory StackToAssembly
imports FlatStackLanguage "../BranchingAssembly/BranchingAssemblyLanguage" "../Utilities/Iterate"
begin

definition sp_to_D :: "computation \<Rightarrow> b_assembly list" where
  "sp_to_D cmp = [CBAssm {A} (Reg M), CBAssm {D} cmp, ABAssm 0]"

definition D_to_sp :: "b_assembly list" where
  "D_to_sp = [CBAssm {A} (Reg M), CBAssm {M} (Reg D), ABAssm 0]"

definition boolify_D :: "comparison \<Rightarrow> b_assembly list" where
  "boolify_D jmp = [IBAssm {jmp} [ABAssm 0, CBAssm {D} One] [ABAssm 0, CBAssm {D} Zero]]"

primrec instruction_conv :: "flat_stack_instruction \<Rightarrow> b_assembly list" where
  "instruction_conv FAdd = sp_to_D (Reg M) @ [CBAssm {M} (Decr M)] @ sp_to_D DPlusM @ D_to_sp"
| "instruction_conv FSub = sp_to_D (Reg M) @ [CBAssm {M} (Decr M)] @ sp_to_D MMinusD @ D_to_sp"
| "instruction_conv FNeg = sp_to_D (NegR M) @ D_to_sp"
| "instruction_conv FEq = 
    sp_to_D (Reg M) @ [CBAssm {M} (Decr M)] @ sp_to_D MMinusD @ boolify_D EQ @ D_to_sp"
| "instruction_conv FGt =
    sp_to_D (Reg M) @ [CBAssm {M} (Decr M)] @ sp_to_D MMinusD @ boolify_D GT @ D_to_sp"
| "instruction_conv FLt =
    sp_to_D (Reg M) @ [CBAssm {M} (Decr M)] @ sp_to_D MMinusD @ boolify_D LT @ D_to_sp"
| "instruction_conv FAnd = sp_to_D (Reg M) @ [CBAssm {M} (Decr M)] @ sp_to_D DAndM @ D_to_sp"
| "instruction_conv FOr = sp_to_D (Reg M) @ [CBAssm {M} (Decr M)] @ sp_to_D DOrM @ D_to_sp"
| "instruction_conv FNot = sp_to_D (NotR M) @ D_to_sp"
| "instruction_conv FPrint = sp_to_D (Reg M) @ [PBAssm, CBAssm {M} (Decr M)]"

definition program_convert :: "flat_stack_program \<Rightarrow> b_assembly_program" where
  "program_convert \<Pi> = map_option (\<lambda>(\<pi>, s). (ABAssm 0 # concat (map instruction_conv \<pi>), s)) o \<Pi>"

primrec stack_to_mem :: "int list \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> nat \<Rightarrow> int" where
  "stack_to_mem [] \<mu> k = (if k = 0 then 0 else \<mu> k)"
| "stack_to_mem (i # is) \<mu> k = (
    if k = 0 then 1 + int (length is)
    else if k = Suc (length is) then i
    else stack_to_mem is \<mu> k)"

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

lemma [simp]: "stack_to_mem \<sigma> \<mu> 0 = int (length \<sigma>)"
  by (induction \<sigma>) simp_all

lemma stack_same: "k > 0 \<Longrightarrow> k \<le> length \<sigma> \<Longrightarrow> stack_to_mem \<sigma> \<mu> k = stack_to_mem \<sigma> \<mu>' k"
  by (induction \<sigma>) simp_all

lemma [simp]: "k > length \<sigma> \<Longrightarrow> stack_to_mem \<sigma> \<mu> k = \<mu> k"
  by (induction \<sigma>) simp_all

lemma [simp]: "(stack_to_mem (a # \<sigma>) \<mu>)(nat (1 + int (length \<sigma>)) := b) = stack_to_mem (b # \<sigma>) \<mu>"
  proof
    fix x
    show "((stack_to_mem (a # \<sigma>) \<mu>)(nat (1 + int (length \<sigma>)) := b)) x = stack_to_mem (b # \<sigma>) \<mu> x" 
      by auto
  qed

lemma [simp]: "(stack_to_mem (i1 # \<sigma>) \<mu>)(0 := int (length \<sigma>)) = 
    stack_to_mem \<sigma> (stack_to_mem (i1 # \<sigma>) \<mu>)"
  proof
    fix x
    show "((stack_to_mem (i1 # \<sigma>) \<mu>)(0 := int (length \<sigma>))) x = 
        stack_to_mem \<sigma> (stack_to_mem (i1 # \<sigma>) \<mu>) x" 
      by (cases "x > length \<sigma>") (simp_all add: stack_same)
  qed

lemma [simp]: "(stack_to_mem (i1 # i2 # \<sigma>) \<mu>)(0 := 1 + int (length \<sigma>)) = 
    stack_to_mem (i2 # \<sigma>) (stack_to_mem (i1 # i2 # \<sigma>) \<mu>)"
  proof
    fix x
    show "((stack_to_mem (i1 # i2 # \<sigma>) \<mu>)(0 := 1 + int (length \<sigma>))) x = 
        stack_to_mem (i2 # \<sigma>) (stack_to_mem (i1 # i2 # \<sigma>) \<mu>) x"
      by (cases "x > length \<sigma>") (simp_all add: stack_same)
  qed

lemma eval_sp_to_D: "iterate (eval_b_assembly \<Pi>) 
    (stack_to_mem (i1 # \<sigma>) \<mu>, Some 0, d, sp_to_D cmp @ \<pi>, s, \<omega>) 
    (stack_to_mem (i1 # \<sigma>) \<mu>, Some 0, compute cmp i1 (1 + int (length \<sigma>)) d, \<pi>, s, \<omega>)"
  proof (unfold sp_to_D_def)
    let ?\<mu> = "stack_to_mem (i1 # \<sigma>) \<mu>"
    let ?\<Sigma>\<^sub>0 = "(?\<mu>, Some 0, d, [CBAssm {A} (Reg M), CBAssm {D} cmp, ABAssm 0] @ \<pi>, s, \<omega>)"
    let ?\<Sigma>\<^sub>1 = "(?\<mu>, Some (?\<mu> 0), d, [CBAssm {D} cmp, ABAssm 0] @ \<pi>, s, \<omega>)"
    let ?\<Sigma>\<^sub>2 = "(?\<mu>, Some (?\<mu> 0), compute cmp i1 (1 + int (length \<sigma>)) d, [ABAssm 0] @ \<pi>, s, \<omega>)"
    let ?\<Sigma>\<^sub>3 = "(?\<mu>, Some 0, compute cmp i1 (1 + int (length \<sigma>)) d, \<pi>, s, \<omega>)"
    have step1: "eval_b_assembly \<Pi> ?\<Sigma>\<^sub>0 = Some ?\<Sigma>\<^sub>1" by simp
    have step2: "eval_b_assembly \<Pi> ?\<Sigma>\<^sub>1 = Some ?\<Sigma>\<^sub>2" by auto
    have "eval_b_assembly \<Pi> ?\<Sigma>\<^sub>2 = Some ?\<Sigma>\<^sub>3" by simp
    with step1 step2 iter_two iter_prestep show "iterate (eval_b_assembly \<Pi>) ?\<Sigma>\<^sub>0 ?\<Sigma>\<^sub>3" by fast
  qed

lemma eval_D_to_sp: "iterate (eval_b_assembly \<Pi>) 
    (stack_to_mem (i1 # \<sigma>) \<mu>, Some 0, d, D_to_sp @ \<pi>, s, \<omega>) 
    (stack_to_mem (d # \<sigma>) \<mu>, Some 0, d, \<pi>, s, \<omega>)"
  proof (unfold D_to_sp_def)
    let ?\<Sigma>\<^sub>0 = "(stack_to_mem (i1 # \<sigma>) \<mu>, Some 0, d, 
      [CBAssm {A} (Reg M), CBAssm {M} (Reg D), ABAssm 0] @ \<pi>, s, \<omega>)"
    let ?\<Sigma>\<^sub>1 = "(stack_to_mem (i1 # \<sigma>) \<mu>, Some (1 + int (length \<sigma>)), d, 
      [CBAssm {M} (Reg D), ABAssm 0] @ \<pi>, s, \<omega>)"
    let ?\<Sigma>\<^sub>2 = "(stack_to_mem (d # \<sigma>) \<mu>, Some (1 + int (length \<sigma>)), d, [ABAssm 0] @ \<pi>, s, \<omega>)"
    let ?\<Sigma>\<^sub>3 = "(stack_to_mem (d # \<sigma>) \<mu>, Some 0, d, \<pi>, s, \<omega>)"
    have step1: "eval_b_assembly \<Pi> ?\<Sigma>\<^sub>0 = Some ?\<Sigma>\<^sub>1" by simp
    have step2: "eval_b_assembly \<Pi> ?\<Sigma>\<^sub>1 = Some ?\<Sigma>\<^sub>2" by simp
    have "eval_b_assembly \<Pi> ?\<Sigma>\<^sub>2 = Some ?\<Sigma>\<^sub>3" by simp
    with step1 step2 iter_two iter_prestep show "iterate (eval_b_assembly \<Pi>) ?\<Sigma>\<^sub>0 ?\<Sigma>\<^sub>3" by fast
  qed

lemma eval_boolify_D: "iterate (eval_b_assembly \<Pi>) 
    (\<sigma>, Some 0, d, boolify_D jmp @ \<pi>, s, \<omega>) 
    (\<sigma>, Some 0, unboolify (compare d {jmp}), \<pi>, s, \<omega>)"
  proof (unfold boolify_D_def)
    let ?\<Sigma>\<^sub>0 = "(\<sigma>, Some 0, d, [IBAssm {jmp} [ABAssm 0, CBAssm {D} One] [ABAssm 0, CBAssm {D} Zero]] @ \<pi>, s, \<omega>)"
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
        sp_to_D (Reg M) @ [CBAssm {M} (Decr M)] @ sp_to_D DPlusM @ D_to_sp @ 
          concat (map instruction_conv \<pi>), s, \<omega>)" by fastforce
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    let ?\<mu> = "stack_to_mem (i1 # i2 # \<sigma>) \<mu>"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(?\<mu>, Some 0, i1, [CBAssm {M} (Decr M)] @ sp_to_D DPlusM @ D_to_sp @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(stack_to_mem (i2 # \<sigma>) ?\<mu>, Some 0, i1, sp_to_D DPlusM @ D_to_sp @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>3 = "(stack_to_mem (i2 # \<sigma>) ?\<mu>, Some 0, i1 + i2, D_to_sp @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>4 = "(stack_to_mem ((i1 + i2) # \<sigma>) ?\<mu>, Some 0, i1 + i2, ?\<pi>', s, \<omega>)"
    have X: "?\<Sigma>\<^sub>A\<^sub>4 \<in> state_convert ((i1 + i2) # \<sigma>, \<pi>, s, \<omega>)" by auto
    from S eval_sp_to_D have step1: "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>1" 
      by fastforce
    have step2: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>1 = Some ?\<Sigma>\<^sub>A\<^sub>2" by simp
    from eval_sp_to_D have step3: "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>2 ?\<Sigma>\<^sub>A\<^sub>3" 
      by fastforce
    from eval_D_to_sp have "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>3 ?\<Sigma>\<^sub>A\<^sub>4" by simp
    with step1 step2 step3 iter_one X show ?case by fast
  next case (evf_sub \<Pi> i1 i2 \<sigma> \<pi> s \<omega>)
    then obtain d \<mu> where S: "\<Sigma>\<^sub>A = 
      (stack_to_mem (i1 # i2 # \<sigma>) \<mu>, Some 0, d, 
        sp_to_D (Reg M) @ [CBAssm {M} (Decr M)] @ sp_to_D MMinusD @ D_to_sp @ 
          concat (map instruction_conv \<pi>), s, \<omega>)" by fastforce
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    let ?\<mu> = "stack_to_mem (i1 # i2 # \<sigma>) \<mu>"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(?\<mu>, Some 0, i1, [CBAssm {M} (Decr M)] @ sp_to_D MMinusD @ D_to_sp @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(stack_to_mem (i2 # \<sigma>) ?\<mu>, Some 0, i1, sp_to_D MMinusD @ D_to_sp @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>3 = "(stack_to_mem (i2 # \<sigma>) ?\<mu>, Some 0, i2 - i1, D_to_sp @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>4 = "(stack_to_mem ((i2 - i1) # \<sigma>) ?\<mu>, Some 0, i2 - i1, ?\<pi>', s, \<omega>)"
    have X: "?\<Sigma>\<^sub>A\<^sub>4 \<in> state_convert ((i2 - i1) # \<sigma>, \<pi>, s, \<omega>)" by auto
    from S eval_sp_to_D have step1: "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>1" 
      by fastforce
    have step2: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>1 = Some ?\<Sigma>\<^sub>A\<^sub>2" by simp
    from eval_sp_to_D have step3: "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>2 ?\<Sigma>\<^sub>A\<^sub>3" 
      by fastforce
    from eval_D_to_sp have "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>3 ?\<Sigma>\<^sub>A\<^sub>4" by fastforce
    with step1 step2 step3 iter_one X show ?case by fast
  next case (evf_neg \<Pi> i1 \<sigma> \<pi> s \<omega>)
    then obtain d \<mu> where S: "\<Sigma>\<^sub>A = 
      (stack_to_mem (i1 # \<sigma>) \<mu>, Some 0, d, 
        sp_to_D (NegR M) @ D_to_sp @ concat (map instruction_conv \<pi>), s, \<omega>)" by fastforce
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(stack_to_mem (i1 # \<sigma>) \<mu>, Some 0, -i1, D_to_sp @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(stack_to_mem (-i1 # \<sigma>) \<mu>, Some 0, -i1, ?\<pi>', s, \<omega>)"
    have X: "?\<Sigma>\<^sub>A\<^sub>2 \<in> state_convert (-i1 # \<sigma>, \<pi>, s, \<omega>)" by auto
    from S eval_sp_to_D have step1: "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>1" 
      by fastforce
    from eval_D_to_sp have "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>1 ?\<Sigma>\<^sub>A\<^sub>2" by simp
    with step1 X show ?case by fast
  next case (evf_eq \<Pi> i1 i2 \<sigma> \<pi> s \<omega>)
    then obtain d \<mu> where S: "\<Sigma>\<^sub>A = 
      (stack_to_mem (i1 # i2 # \<sigma>) \<mu>, Some 0, d, 
        sp_to_D (Reg M) @ [CBAssm {M} (Decr M)] @ sp_to_D MMinusD @ boolify_D EQ @ D_to_sp @
          concat (map instruction_conv \<pi>), s, \<omega>)" by fastforce
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    let ?\<mu> = "stack_to_mem (i1 # i2 # \<sigma>) \<mu>"
    let ?result = "unboolify (i2 = i1)"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(?\<mu>, Some 0, i1, 
      [CBAssm {M} (Decr M)] @ sp_to_D MMinusD @ boolify_D EQ @ D_to_sp @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(stack_to_mem (i2 # \<sigma>) ?\<mu>, Some 0, i1, 
      sp_to_D MMinusD @ boolify_D EQ @ D_to_sp @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>3 = "(stack_to_mem (i2 # \<sigma>) ?\<mu>, Some 0, i2 - i1, boolify_D EQ @ D_to_sp @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>4 = "(stack_to_mem (i2 # \<sigma>) ?\<mu>, Some 0, ?result, D_to_sp @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>5 = "(stack_to_mem (?result # \<sigma>) ?\<mu>, Some 0, ?result, ?\<pi>', s, \<omega>)"
    have X: "?\<Sigma>\<^sub>A\<^sub>5 \<in> state_convert (?result # \<sigma>, \<pi>, s, \<omega>)" by auto
    from S eval_sp_to_D have step1: "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>1" 
      by fastforce
    have step2: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>1 = Some ?\<Sigma>\<^sub>A\<^sub>2" by simp
    from eval_sp_to_D have step3: "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>2 ?\<Sigma>\<^sub>A\<^sub>3" 
      by fastforce
    from eval_boolify_D have step4: "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>3 ?\<Sigma>\<^sub>A\<^sub>4" 
      by fastforce
    from eval_D_to_sp have "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>4 ?\<Sigma>\<^sub>A\<^sub>5" by simp
    with X step1 step2 step3 step4 iter_one show ?case by fast
  next case (evf_gt \<Pi> i1 i2 \<sigma> \<pi> s \<omega>)
    then obtain d \<mu> where S: "\<Sigma>\<^sub>A = 
      (stack_to_mem (i1 # i2 # \<sigma>) \<mu>, Some 0, d, 
        sp_to_D (Reg M) @ [CBAssm {M} (Decr M)] @ sp_to_D MMinusD @ boolify_D GT @ D_to_sp @
          concat (map instruction_conv \<pi>), s, \<omega>)" by fastforce
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    let ?\<mu> = "stack_to_mem (i1 # i2 # \<sigma>) \<mu>"
    let ?result = "unboolify (i2 > i1)"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(?\<mu>, Some 0, i1,
      [CBAssm {M} (Decr M)] @ sp_to_D MMinusD @ boolify_D GT @ D_to_sp @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(stack_to_mem (i2 # \<sigma>) ?\<mu>, Some 0, i1, 
      sp_to_D MMinusD @ boolify_D GT @ D_to_sp @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>3 = "(stack_to_mem (i2 # \<sigma>) ?\<mu>, Some 0, i2 - i1, boolify_D GT @ D_to_sp @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>4' = "(stack_to_mem (i2 # \<sigma>) ?\<mu>, Some 0, unboolify (i2 - i1 > 0), D_to_sp @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>4 = "(stack_to_mem (i2 # \<sigma>) ?\<mu>, Some 0, ?result, D_to_sp @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>5 = "(stack_to_mem (?result # \<sigma>) ?\<mu>, Some 0, ?result, ?\<pi>', s, \<omega>)"
    have X: "?\<Sigma>\<^sub>A\<^sub>5 \<in> state_convert (?result # \<sigma>, \<pi>, s, \<omega>)" by auto
    from S eval_sp_to_D have step1: "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>1" 
      by fastforce
    have step2: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>1 = Some ?\<Sigma>\<^sub>A\<^sub>2" by simp
    from eval_sp_to_D have step3: "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>2 ?\<Sigma>\<^sub>A\<^sub>3" 
      by fastforce
    from eval_boolify_D have "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>3 ?\<Sigma>\<^sub>A\<^sub>4'" 
      by fastforce
    moreover have "?\<Sigma>\<^sub>A\<^sub>4' = ?\<Sigma>\<^sub>A\<^sub>4" by smt
    ultimately have step4: "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>3 ?\<Sigma>\<^sub>A\<^sub>4" by simp
    from eval_D_to_sp have "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>4 ?\<Sigma>\<^sub>A\<^sub>5" by simp
    with X step1 step2 step3 step4 iter_one show ?case by fast
  next case (evf_lt \<Pi> i1 i2 \<sigma> \<pi> s \<omega>)
    then obtain d \<mu> where S: "\<Sigma>\<^sub>A = 
      (stack_to_mem (i1 # i2 # \<sigma>) \<mu>, Some 0, d, 
        sp_to_D (Reg M) @ [CBAssm {M} (Decr M)] @ sp_to_D MMinusD @ boolify_D LT @ D_to_sp @
          concat (map instruction_conv \<pi>), s, \<omega>)" by fastforce
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    let ?\<mu> = "stack_to_mem (i1 # i2 # \<sigma>) \<mu>"
    let ?result = "unboolify (i2 < i1)"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(?\<mu>, Some 0, i1, 
      [CBAssm {M} (Decr M)] @ sp_to_D MMinusD @ boolify_D LT @ D_to_sp @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(stack_to_mem (i2 # \<sigma>) ?\<mu>, Some 0, i1, 
      sp_to_D MMinusD @ boolify_D LT @ D_to_sp @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>3 = "(stack_to_mem (i2 # \<sigma>) ?\<mu>, Some 0, i2 - i1, boolify_D LT @ D_to_sp @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>4 = "(stack_to_mem (i2 # \<sigma>) ?\<mu>, Some 0, ?result, D_to_sp @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>5 = "(stack_to_mem (?result # \<sigma>) ?\<mu>, Some 0, ?result, ?\<pi>', s, \<omega>)"
    have X: "?\<Sigma>\<^sub>A\<^sub>5 \<in> state_convert (?result # \<sigma>, \<pi>, s, \<omega>)" by auto
    from S eval_sp_to_D have step1: "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>1" 
      by fastforce
    have step2: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>1 = Some ?\<Sigma>\<^sub>A\<^sub>2" by simp
    from eval_sp_to_D have step3: "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>2 ?\<Sigma>\<^sub>A\<^sub>3" 
      by fastforce
    from eval_boolify_D have step4: "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>3 ?\<Sigma>\<^sub>A\<^sub>4" 
      by fastforce
    from eval_D_to_sp have "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>4 ?\<Sigma>\<^sub>A\<^sub>5" by simp
    with X step1 step2 step3 step4 iter_one show ?case by fast
  next case (evf_and \<Pi> i1 i2 \<sigma> \<pi> s \<omega>)
    then obtain d \<mu> where S: "\<Sigma>\<^sub>A = 
      (stack_to_mem (i1 # i2 # \<sigma>) \<mu>, Some 0, d, 
        sp_to_D (Reg M) @ [CBAssm {M} (Decr M)] @ sp_to_D DAndM @ D_to_sp @ 
          concat (map instruction_conv \<pi>), s, \<omega>)" by fastforce
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    let ?\<mu> = "stack_to_mem (i1 # i2 # \<sigma>) \<mu>"
    let ?result = "unboolify (boolify i1 \<and> boolify i2)"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(?\<mu>, Some 0, i1, [CBAssm {M} (Decr M)] @ sp_to_D DAndM @ D_to_sp @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(stack_to_mem (i2 # \<sigma>) ?\<mu>, Some 0, i1, sp_to_D DAndM @ D_to_sp @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>3 = "(stack_to_mem (i2 # \<sigma>) ?\<mu>, Some 0, ?result, D_to_sp @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>4 = "(stack_to_mem (?result # \<sigma>) ?\<mu>, Some 0, ?result, ?\<pi>', s, \<omega>)"
    have X: "?\<Sigma>\<^sub>A\<^sub>4 \<in> state_convert (?result # \<sigma>, \<pi>, s, \<omega>)" by auto
    from S eval_sp_to_D have step1: "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>1" 
      by fastforce
    have step2: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>1 = Some ?\<Sigma>\<^sub>A\<^sub>2" by simp
    from eval_sp_to_D have step3: "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>2 ?\<Sigma>\<^sub>A\<^sub>3" 
      by fastforce
    from eval_D_to_sp have "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>3 ?\<Sigma>\<^sub>A\<^sub>4" by simp
    with step1 step2 step3 iter_one X show ?case by fast
  next case (evf_or \<Pi> i1 i2 \<sigma> \<pi> s \<omega>)
    then obtain d \<mu> where S: "\<Sigma>\<^sub>A = 
      (stack_to_mem (i1 # i2 # \<sigma>) \<mu>, Some 0, d, 
        sp_to_D (Reg M) @ [CBAssm {M} (Decr M)] @ sp_to_D DOrM @ D_to_sp @ 
          concat (map instruction_conv \<pi>), s, \<omega>)" by fastforce
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    let ?\<mu> = "stack_to_mem (i1 # i2 # \<sigma>) \<mu>"
    let ?result = "unboolify (boolify i1 \<or> boolify i2)"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(?\<mu>, Some 0, i1, [CBAssm {M} (Decr M)] @ sp_to_D DOrM @ D_to_sp @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(stack_to_mem (i2 # \<sigma>) ?\<mu>, Some 0, i1, sp_to_D DOrM @ D_to_sp @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>3 = "(stack_to_mem (i2 # \<sigma>) ?\<mu>, Some 0, ?result, D_to_sp @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>4 = "(stack_to_mem (?result # \<sigma>) ?\<mu>, Some 0, ?result, ?\<pi>', s, \<omega>)"
    have X: "?\<Sigma>\<^sub>A\<^sub>4 \<in> state_convert (?result # \<sigma>, \<pi>, s, \<omega>)" by auto
    from S eval_sp_to_D have step1: "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>1" 
      by fastforce
    have step2: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>1 = Some ?\<Sigma>\<^sub>A\<^sub>2" by simp
    from eval_sp_to_D have step3: "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>2 ?\<Sigma>\<^sub>A\<^sub>3" 
      by fastforce
    from eval_D_to_sp have "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>3 ?\<Sigma>\<^sub>A\<^sub>4" by simp
    with step1 step2 step3 iter_one X show ?case by fast
  next case (evf_not \<Pi> i1 \<sigma> \<pi> s \<omega>)
    then obtain d \<mu> where S: "\<Sigma>\<^sub>A = 
      (stack_to_mem (i1 # \<sigma>) \<mu>, Some 0, d, 
        sp_to_D (NotR M) @ D_to_sp @ concat (map instruction_conv \<pi>), s, \<omega>)" by fastforce
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    let ?result = "unboolify (\<not> boolify i1)"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(stack_to_mem (i1 # \<sigma>) \<mu>, Some 0, ?result, D_to_sp @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(stack_to_mem (?result # \<sigma>) \<mu>, Some 0, ?result, ?\<pi>', s, \<omega>)"
    have X: "?\<Sigma>\<^sub>A\<^sub>2 \<in> state_convert (?result # \<sigma>, \<pi>, s, \<omega>)" by auto
    from S eval_sp_to_D have step1: "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>1" 
      by fastforce
    from eval_D_to_sp have "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>1 ?\<Sigma>\<^sub>A\<^sub>2" by simp
    with step1 X show ?case by fast
  next case (evf_print \<Pi> i1 \<sigma> \<pi> s \<omega>)
    then obtain d \<mu> where S: "\<Sigma>\<^sub>A = 
      (stack_to_mem (i1 # \<sigma>) \<mu>, Some 0, d, 
        sp_to_D (Reg M) @ [PBAssm, CBAssm {M} (Decr M)] @ concat (map instruction_conv \<pi>), s, \<omega>)" 
      by fastforce
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(stack_to_mem (i1 # \<sigma>) \<mu>, Some 0, i1, [PBAssm, CBAssm {M} (Decr M)] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(stack_to_mem (i1 # \<sigma>) \<mu>, Some 0, i1, [CBAssm {M} (Decr M)] @ ?\<pi>', s, i1 # \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>3 = "(stack_to_mem \<sigma> (stack_to_mem (i1 # \<sigma>) \<mu>), Some 0, i1, ?\<pi>', s, i1 # \<omega>)"
    have X: "?\<Sigma>\<^sub>A\<^sub>3 \<in> state_convert (\<sigma>, \<pi>, s, i1 # \<omega>)" by auto
    from S eval_sp_to_D have step1: "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>1" 
      by fastforce
    have step2: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>1 = Some ?\<Sigma>\<^sub>A\<^sub>2" by simp
    have "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>2 = Some ?\<Sigma>\<^sub>A\<^sub>3" by simp
    with step1 step2 X iter_two show ?case by fast
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