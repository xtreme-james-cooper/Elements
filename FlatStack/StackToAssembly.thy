theory StackToAssembly
imports FlatStackLanguage "../BranchingAssembly/BranchingAssemblyLanguage" "../Utilities/Iterate"
begin

primrec instruction_conv :: "flat_stack_instruction \<Rightarrow> b_assembly list" where
  "instruction_conv FAdd = [
    CBAssm {A} (Reg M), 
    CBAssm {D} (Reg M), 
    ABAssm 0, 
    CBAssm {A, M} (Decr M), 
    CBAssm {M} DPlusM, 
    ABAssm 0]"
| "instruction_conv FSub = [
    CBAssm {A} (Reg M),
    CBAssm {D} (Reg M), 
    ABAssm 0, 
    CBAssm {A, M} (Decr M), 
    CBAssm {M} MMinusD, 
    ABAssm 0]"
| "instruction_conv FNeg = [
    CBAssm {A} (Reg M), 
    CBAssm {M} (NegR M), 
    ABAssm 0]"
| "instruction_conv FEq = [
    CBAssm {A} (Reg M),
    CBAssm {D} (Reg M), 
    ABAssm 0, 
    CBAssm {A, M} (Decr M), 
    CBAssm {D} MMinusD, 
    IBAssm {EQ} 
      [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} One] 
      [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} Zero],
    ABAssm 0]"
| "instruction_conv FGt = [
    CBAssm {A} (Reg M),
    CBAssm {D} (Reg M), 
    ABAssm 0, 
    CBAssm {A, M} (Decr M), 
    CBAssm {D} MMinusD, 
    IBAssm {GT} 
      [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} One] 
      [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} Zero],
    ABAssm 0]"
| "instruction_conv FLt = [
    CBAssm {A} (Reg M),
    CBAssm {D} (Reg M), 
    ABAssm 0, 
    CBAssm {A, M} (Decr M), 
    CBAssm {D} MMinusD, 
    IBAssm {LT} 
      [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} One] 
      [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} Zero],
    ABAssm 0]"
| "instruction_conv FAnd = [
    CBAssm {A} (Reg M), 
    CBAssm {D} (Reg M), 
    ABAssm 0, 
    CBAssm {A, M} (Decr M), 
    CBAssm {M} DAndM, 
    ABAssm 0]"
| "instruction_conv FOr = [
    CBAssm {A} (Reg M), 
    CBAssm {D} (Reg M), 
    ABAssm 0, 
    CBAssm {A, M} (Decr M), 
    CBAssm {M} DOrM, 
    ABAssm 0]"
| "instruction_conv FNot = [
    CBAssm {A} (Reg M), 
    CBAssm {M} (NotR M), 
    ABAssm 0]"
| "instruction_conv FPrint = [
    CBAssm {A} (Reg M), 
    CBAssm {D} (Reg M),
    PBAssm,
    ABAssm 0, 
    CBAssm {M} (Decr M)]"

definition program_convert :: "flat_stack_program \<Rightarrow> b_assembly_program" where
  "program_convert \<Pi> = map_option (\<lambda>(\<pi>, s). (ABAssm 0 # concat (map instruction_conv \<pi>), s)) o \<Pi>"

primrec stack_to_mem :: "int list \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int" where
  "stack_to_mem [] \<mu> k = (if k = 0 then 0 else \<mu> k)"
| "stack_to_mem (i # is) \<mu> k = (
    if k = 0 then 1 + int (length is)
    else if k = 1 + int (length is) then i
    else stack_to_mem is \<mu> k)"

fun state_convert :: "flat_stack_state \<Rightarrow> b_assembly_state set" where
  "state_convert (\<sigma>, \<pi>, s, \<omega>) = 
    {(stack_to_mem \<sigma> \<mu>, Some 0, d, concat (map instruction_conv \<pi>), s, \<omega>) | d \<mu>. True }"

(* conversion correctness *)

lemma [simp]: "dom (program_convert \<Pi>) = dom \<Pi>"
  by (auto simp add: program_convert_def)

lemma [simp]: "\<Pi> s = Some (\<pi>, s') \<Longrightarrow> 
    program_convert \<Pi> s = Some (ABAssm 0 # concat (map instruction_conv \<pi>), s')"
  by (simp add: program_convert_def)

lemma [simp]: "stack_to_mem \<sigma> \<mu> 0 = int (length \<sigma>)"
  by (induction \<sigma>) simp_all

lemma [simp]: "k < 0 \<Longrightarrow> stack_to_mem \<sigma> \<mu> k = \<mu> k"
  by (induction \<sigma>) simp_all

lemma stack_same: "k > 0 \<Longrightarrow> k \<le> int (length \<sigma>) \<Longrightarrow> stack_to_mem \<sigma> \<mu> k = stack_to_mem \<sigma> \<mu>' k"
  by (induction \<sigma>) simp_all

lemma [simp]: "k > int (length \<sigma>) \<Longrightarrow> stack_to_mem \<sigma> \<mu> k = \<mu> k"
  by (induction \<sigma>) simp_all

lemma [simp]: "(stack_to_mem (i1 # \<sigma>) \<mu>)(0 := int (length \<sigma>)) = 
    stack_to_mem \<sigma> (stack_to_mem (i1 # \<sigma>) \<mu>)"
  proof
    fix x
    show "((stack_to_mem (i1 # \<sigma>) \<mu>)(0 := int (length \<sigma>))) x = 
        stack_to_mem \<sigma> (stack_to_mem (i1 # \<sigma>) \<mu>) x" 
      proof (cases "x < 0")
      case True
        thus ?thesis by simp
      next case False
        with stack_same show ?thesis by (cases "x > int (length \<sigma>)") simp_all
      qed
  qed

lemma [simp]: "(stack_to_mem (i2 # i3 # \<sigma>) \<mu>)(0 := 1 + int (length \<sigma>), 1 + int (length \<sigma>) := i1) =
    stack_to_mem (i1 # \<sigma>) (stack_to_mem (i2 # i3 # \<sigma>) \<mu>)"
  proof
    fix x
    show "((stack_to_mem (i2 # i3 # \<sigma>) \<mu>)(0 := 1 + int (length \<sigma>), 1 + int (length \<sigma>) := i1)) x = 
        stack_to_mem (i1 # \<sigma>) (stack_to_mem (i2 # i3 # \<sigma>) \<mu>) x" 
      proof (cases "x < 0")
      case True
        thus ?thesis by simp
      next case False
        with stack_same show ?thesis by (cases "x > int (length \<sigma>)") simp_all
      qed
  qed

lemma [simp]: "\<Sigma>\<^sub>B \<in> state_convert \<Sigma>\<^sub>S \<Longrightarrow> b_assembly_output \<Sigma>\<^sub>B = flat_stack_output \<Sigma>\<^sub>S"
  by (induction \<Sigma>\<^sub>S rule: flat_stack_output.induct, induction \<Sigma>\<^sub>B rule: b_assembly_output.induct) simp

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
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    from evf_add obtain d \<mu> where M: "\<Sigma>\<^sub>A = (stack_to_mem (i1 # i2 # \<sigma>) \<mu>, Some 0, d, 
      [CBAssm {A} (Reg M), CBAssm {D} (Reg M), ABAssm 0, 
       CBAssm {A, M} (Decr M), CBAssm {M} DPlusM, ABAssm 0] @ ?\<pi>', s, \<omega>)" by fastforce
    let ?\<mu> = "stack_to_mem (i1 # i2 # \<sigma>) \<mu>"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(?\<mu>, Some (?\<mu> 0), d, 
      [CBAssm {D} (Reg M), ABAssm 0, CBAssm {A, M} (Decr M), 
       CBAssm {M} DPlusM, ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(?\<mu>, Some (?\<mu> 0), ?\<mu> (?\<mu> 0), 
      [ABAssm 0, CBAssm {A, M} (Decr M), CBAssm {M} DPlusM, ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>3 = "(?\<mu>, Some 0, ?\<mu> (?\<mu> 0), 
      [CBAssm {A, M} (Decr M), CBAssm {M} DPlusM, ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>4 = "(?\<mu>(0 := ?\<mu> 0 - 1), Some (?\<mu> 0 - 1), ?\<mu> (?\<mu> 0), 
      [CBAssm {M} DPlusM, ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>5 = "(stack_to_mem ((i1 + i2) # \<sigma>) ?\<mu>, Some (?\<mu> 0 - 1), ?\<mu> (?\<mu> 0), 
      [ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>6 = "(stack_to_mem ((i1 + i2) # \<sigma>) ?\<mu>, Some 0, ?\<mu> (?\<mu> 0), ?\<pi>', s, \<omega>)"
    from M have step1: "eval_b_assembly (program_convert \<Pi>) \<Sigma>\<^sub>A = Some ?\<Sigma>\<^sub>A\<^sub>1" by simp
    have step2: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>1 = Some ?\<Sigma>\<^sub>A\<^sub>2" by simp
    have step3: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>2 = Some ?\<Sigma>\<^sub>A\<^sub>3" by simp
    have step4: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>3 = Some ?\<Sigma>\<^sub>A\<^sub>4" by (simp add: Let_def)
    have step5: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>4 = Some ?\<Sigma>\<^sub>A\<^sub>5" by simp
    have step6: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>5 = Some ?\<Sigma>\<^sub>A\<^sub>6" by simp
    from iter_two iter_prestep step1 step2 step3 have
      "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>3" by fast
    moreover from iter_two iter_prestep step4 step5 step6 have
      "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>3 ?\<Sigma>\<^sub>A\<^sub>6" by fast
    ultimately have X: "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>6" by fast
    have "?\<Sigma>\<^sub>A\<^sub>6 \<in> state_convert ((i2 + i1) # \<sigma>, \<pi>, s, \<omega>)" by fastforce
    with X show ?case by metis
  next case (evf_sub \<Pi> i1 i2 \<sigma> \<pi> s \<omega>)
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    from evf_sub obtain d \<mu> where M: "\<Sigma>\<^sub>A = (stack_to_mem (i1 # i2 # \<sigma>) \<mu>, Some 0, d, 
      [CBAssm {A} (Reg M), CBAssm {D} (Reg M), ABAssm 0, 
       CBAssm {A, M} (Decr M), CBAssm {M} MMinusD, ABAssm 0] @ ?\<pi>', s, \<omega>)" by fastforce
    let ?\<mu> = "stack_to_mem (i1 # i2 # \<sigma>) \<mu>"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(?\<mu>, Some (?\<mu> 0), d, 
      [CBAssm {D} (Reg M), ABAssm 0, 
       CBAssm {A, M} (Decr M), CBAssm {M} MMinusD, ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(?\<mu>, Some (?\<mu> 0), ?\<mu> (?\<mu> 0), 
      [ABAssm 0, CBAssm {A, M} (Decr M), CBAssm {M} MMinusD, ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>3 = "(?\<mu>, Some 0, ?\<mu> (?\<mu> 0), 
      [CBAssm {A, M} (Decr M), CBAssm {M} MMinusD, ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>4 = "(?\<mu>(0 := ?\<mu> 0 - 1), Some (?\<mu> 0 - 1), ?\<mu> (?\<mu> 0),
      [CBAssm {M} MMinusD, ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>5 = "(stack_to_mem ((i2 - i1) # \<sigma>) ?\<mu>, Some (?\<mu> 0 - 1), ?\<mu> (?\<mu> 0), 
      [ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>6 = "(stack_to_mem ((i2 - i1) # \<sigma>) ?\<mu>, Some 0, ?\<mu> (?\<mu> 0), ?\<pi>', s, \<omega>)"
    from M have step1: "eval_b_assembly (program_convert \<Pi>) \<Sigma>\<^sub>A = Some ?\<Sigma>\<^sub>A\<^sub>1" by simp
    have step2: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>1 = Some ?\<Sigma>\<^sub>A\<^sub>2" by simp
    have step3: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>2 = Some ?\<Sigma>\<^sub>A\<^sub>3" by simp
    have step4: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>3 = Some ?\<Sigma>\<^sub>A\<^sub>4" by (simp add: Let_def)
    have step5: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>4 = Some ?\<Sigma>\<^sub>A\<^sub>5" by simp
    have step6: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>5 = Some ?\<Sigma>\<^sub>A\<^sub>6" by simp
    from iter_two iter_prestep step1 step2 step3 have
      "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>3" by fast
    moreover from iter_two iter_prestep step4 step5 step6 have
      "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>3 ?\<Sigma>\<^sub>A\<^sub>6" by fast
    ultimately have X: "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>6" by fast
    have "?\<Sigma>\<^sub>A\<^sub>6 \<in> state_convert ((i2 - i1) # \<sigma>, \<pi>, s, \<omega>)" by auto
    with X show ?case by metis
  next case (evf_neg \<Pi> i1 \<sigma> \<pi> s \<omega>)
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    from evf_neg obtain d \<mu> where M: "\<Sigma>\<^sub>A = (stack_to_mem (i1 # \<sigma>) \<mu>, Some 0, d, 
      [CBAssm {A} (Reg M), CBAssm {M} (NegR M), ABAssm 0] @ ?\<pi>', s, \<omega>)" by fastforce
    let ?\<mu> = "stack_to_mem (i1 # \<sigma>) \<mu>"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(?\<mu>, Some (?\<mu> 0), d, [CBAssm {M} (NegR M), ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(?\<mu>(?\<mu> 0 := - ?\<mu> (?\<mu> 0)), Some (?\<mu> 0), d, [ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>3 = "(?\<mu>(?\<mu> 0 := - ?\<mu> (?\<mu> 0)), Some 0, d, ?\<pi>', s, \<omega>)"
    from M have step1: "eval_b_assembly (program_convert \<Pi>) \<Sigma>\<^sub>A = Some ?\<Sigma>\<^sub>A\<^sub>1" by simp
    have step2: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>1 = Some ?\<Sigma>\<^sub>A\<^sub>2" by simp
    have "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>2 = Some ?\<Sigma>\<^sub>A\<^sub>3" by simp
    with iter_two iter_prestep step1 step2 have X:
      "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>3" by fast
    have "(stack_to_mem (i1 # \<sigma>) \<mu>)(1 + int (length \<sigma>) := - i1) = stack_to_mem (- i1 # \<sigma>) \<mu>" by auto
    hence "?\<Sigma>\<^sub>A\<^sub>3 \<in> state_convert ((-i1) # \<sigma>, \<pi>, s, \<omega>)" by auto
    with X show ?case by metis
  next case (evf_eq \<Pi> i1 i2 \<sigma> \<pi> s \<omega>)
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    from evf_eq obtain d \<mu> where M: "\<Sigma>\<^sub>A = (stack_to_mem (i1 # i2 # \<sigma>) \<mu>, Some 0, d, 
      [CBAssm {A} (Reg M), CBAssm {D} (Reg M), ABAssm 0, 
       CBAssm {A, M} (Decr M), CBAssm {D} MMinusD, 
       IBAssm {EQ} [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} One] 
                   [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} Zero], ABAssm 0] @ ?\<pi>', s, \<omega>)" 
      by fastforce
    let ?\<mu> = "stack_to_mem (i1 # i2 # \<sigma>) \<mu>"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(?\<mu>, Some (?\<mu> 0), d, 
      [CBAssm {D} (Reg M), ABAssm 0, CBAssm {A, M} (Decr M), CBAssm {D} MMinusD, 
       IBAssm {EQ} [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} One] 
                   [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} Zero], ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(?\<mu>, Some (?\<mu> 0), ?\<mu> (?\<mu> 0), 
      [ABAssm 0, CBAssm {A, M} (Decr M), CBAssm {D} MMinusD, 
       IBAssm {EQ} [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} One] 
                   [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} Zero], ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>3 = "(?\<mu>, Some 0, ?\<mu> (?\<mu> 0), 
      [CBAssm {A, M} (Decr M), CBAssm {D} MMinusD, 
       IBAssm {EQ} [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} One] 
                   [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} Zero], ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>4 = "(?\<mu>(0 := ?\<mu> 0 - 1), Some (?\<mu> 0 - 1), ?\<mu> (?\<mu> 0), 
      [CBAssm {D} MMinusD, IBAssm {EQ} [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} One] 
        [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} Zero], ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>5 = "(?\<mu>(0 := ?\<mu> 0 - 1), Some (?\<mu> 0 - 1), ?\<mu> (?\<mu> 0 - 1) - ?\<mu> (?\<mu> 0), 
      [IBAssm {EQ} [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} One] 
                   [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} Zero], ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>6\<^sub>t = "(?\<mu>(0 := ?\<mu> 0 - 1), None, ?\<mu> (?\<mu> 0 - 1) - ?\<mu> (?\<mu> 0), 
      [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} One, ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>7\<^sub>t = "(?\<mu>(0 := ?\<mu> 0 - 1), Some 0, ?\<mu> (?\<mu> 0 - 1) - ?\<mu> (?\<mu> 0), 
      [CBAssm {A} (Reg M), CBAssm {M} One, ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>8\<^sub>t = "(?\<mu>(0 := ?\<mu> 0 - 1), Some (?\<mu> 0 - 1), ?\<mu> (?\<mu> 0 - 1) - ?\<mu> (?\<mu> 0), 
      [CBAssm {M} One, ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>6\<^sub>f = "(?\<mu>(0 := ?\<mu> 0 - 1), None, ?\<mu> (?\<mu> 0 - 1) - ?\<mu> (?\<mu> 0), 
      [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} Zero, ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>7\<^sub>f = "(?\<mu>(0 := ?\<mu> 0 - 1), Some 0, ?\<mu> (?\<mu> 0 - 1) - ?\<mu> (?\<mu> 0), 
      [CBAssm {A} (Reg M), CBAssm {M} Zero, ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>8\<^sub>f = "(?\<mu>(0 := ?\<mu> 0 - 1), Some (?\<mu> 0 - 1), ?\<mu> (?\<mu> 0 - 1) - ?\<mu> (?\<mu> 0), 
      [CBAssm {M} Zero, ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>9 = "(stack_to_mem (unboolify (i2 = i1) # \<sigma>) ?\<mu>, Some (?\<mu> 0 - 1), 
      ?\<mu> (?\<mu> 0 - 1) - ?\<mu> (?\<mu> 0), [ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>1\<^sub>0 = "(stack_to_mem (unboolify (i2 = i1) # \<sigma>) ?\<mu>, Some 0, 
      ?\<mu> (?\<mu> 0 - 1) - ?\<mu> (?\<mu> 0), ?\<pi>', s, \<omega>)"
    from M have step1: "eval_b_assembly (program_convert \<Pi>) \<Sigma>\<^sub>A = Some ?\<Sigma>\<^sub>A\<^sub>1" by simp
    have step2: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>1 = Some ?\<Sigma>\<^sub>A\<^sub>2" by simp
    have step3: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>2 = Some ?\<Sigma>\<^sub>A\<^sub>3" by simp
    have step4: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>3 = Some ?\<Sigma>\<^sub>A\<^sub>4" by (simp add: Let_def)
    have step5: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>4 = Some ?\<Sigma>\<^sub>A\<^sub>5" by simp
    have step6t: "?\<mu> (?\<mu> 0 - 1) = ?\<mu> (?\<mu> 0) \<Longrightarrow> 
      eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>5 = Some ?\<Sigma>\<^sub>A\<^sub>6\<^sub>t" by simp
    have step7t: "?\<mu> (?\<mu> 0 - 1) = ?\<mu> (?\<mu> 0) \<Longrightarrow> 
      eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>6\<^sub>t = Some ?\<Sigma>\<^sub>A\<^sub>7\<^sub>t" by simp
    have step8t: "?\<mu> (?\<mu> 0 - 1) = ?\<mu> (?\<mu> 0) \<Longrightarrow> 
      eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>7\<^sub>t = Some ?\<Sigma>\<^sub>A\<^sub>8\<^sub>t" by simp
    have step9t: "?\<mu> (?\<mu> 0 - 1) = ?\<mu> (?\<mu> 0) \<Longrightarrow> 
      eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>8\<^sub>t = Some ?\<Sigma>\<^sub>A\<^sub>9" by simp
    have step6f: "?\<mu> (?\<mu> 0 - 1) \<noteq> ?\<mu> (?\<mu> 0) \<Longrightarrow> 
      eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>5 = Some ?\<Sigma>\<^sub>A\<^sub>6\<^sub>f" by simp
    have step7f: "?\<mu> (?\<mu> 0 - 1) \<noteq> ?\<mu> (?\<mu> 0) \<Longrightarrow> 
      eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>6\<^sub>f = Some ?\<Sigma>\<^sub>A\<^sub>7\<^sub>f" by simp
    have step8f: "?\<mu> (?\<mu> 0 - 1) \<noteq> ?\<mu> (?\<mu> 0) \<Longrightarrow> 
      eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>7\<^sub>f = Some ?\<Sigma>\<^sub>A\<^sub>8\<^sub>f" by simp
    have step9f: "?\<mu> (?\<mu> 0 - 1) \<noteq> ?\<mu> (?\<mu> 0) \<Longrightarrow> 
      eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>8\<^sub>f = Some ?\<Sigma>\<^sub>A\<^sub>9" by simp
    have step10: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>9 = Some ?\<Sigma>\<^sub>A\<^sub>1\<^sub>0" by simp
    from iter_two iter_prestep step1 step2 step3 have 
      "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>3" by fast
    with iter_two step4 step5 have Y: 
      "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>5" by fast
    have "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>5 ?\<Sigma>\<^sub>A\<^sub>1\<^sub>0"
      proof (cases "?\<mu> (?\<mu> 0 - 1) = ?\<mu> (?\<mu> 0)")
      case True
        with iter_two iter_prestep step6t step7t step8t have 
          "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>5 ?\<Sigma>\<^sub>A\<^sub>8\<^sub>t" by fast
        with True iter_two step9t step10 show ?thesis by fast
      next case False
        with iter_two iter_prestep step6f step7f step8f have 
          "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>5 ?\<Sigma>\<^sub>A\<^sub>8\<^sub>f" by fast
        with False iter_two step9f step10 show ?thesis by fast
      qed
    with Y iter_many have X: "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>1\<^sub>0" by fast
    have "?\<Sigma>\<^sub>A\<^sub>1\<^sub>0 \<in> state_convert (unboolify (i2 = i1) # \<sigma>, \<pi>, s, \<omega>)" by fastforce
    with X show ?case by metis
  next case (evf_gt \<Pi> i1 i2 \<sigma> \<pi> s \<omega>)
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    from evf_gt obtain d \<mu> where M: "\<Sigma>\<^sub>A = (stack_to_mem (i1 # i2 # \<sigma>) \<mu>, Some 0, d, 
      [CBAssm {A} (Reg M), CBAssm {D} (Reg M), ABAssm 0, 
       CBAssm {A, M} (Decr M), CBAssm {D} MMinusD, 
       IBAssm {GT} [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} One] 
                   [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} Zero], ABAssm 0] @ ?\<pi>', s, \<omega>)" 
      by fastforce
    let ?\<mu> = "stack_to_mem (i1 # i2 # \<sigma>) \<mu>"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(?\<mu>, Some (?\<mu> 0), d, 
      [CBAssm {D} (Reg M), ABAssm 0, CBAssm {A, M} (Decr M), CBAssm {D} MMinusD, 
       IBAssm {GT} [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} One] 
                   [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} Zero], ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(?\<mu>, Some (?\<mu> 0), ?\<mu> (?\<mu> 0), 
      [ABAssm 0, CBAssm {A, M} (Decr M), CBAssm {D} MMinusD, 
       IBAssm {GT} [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} One] 
                   [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} Zero], ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>3 = "(?\<mu>, Some 0, ?\<mu> (?\<mu> 0), 
      [CBAssm {A, M} (Decr M), CBAssm {D} MMinusD, 
       IBAssm {GT} [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} One] 
                   [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} Zero], ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>4 = "(?\<mu>(0 := ?\<mu> 0 - 1), Some (?\<mu> 0 - 1), ?\<mu> (?\<mu> 0), 
      [CBAssm {D} MMinusD, IBAssm {GT} [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} One] 
        [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} Zero], ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>5 = "(?\<mu>(0 := ?\<mu> 0 - 1), Some (?\<mu> 0 - 1), ?\<mu> (?\<mu> 0 - 1) - ?\<mu> (?\<mu> 0), 
      [IBAssm {GT} [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} One] 
                   [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} Zero], ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>6\<^sub>t = "(?\<mu>(0 := ?\<mu> 0 - 1), None, ?\<mu> (?\<mu> 0 - 1) - ?\<mu> (?\<mu> 0), 
      [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} One, ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>7\<^sub>t = "(?\<mu>(0 := ?\<mu> 0 - 1), Some 0, ?\<mu> (?\<mu> 0 - 1) - ?\<mu> (?\<mu> 0), 
      [CBAssm {A} (Reg M), CBAssm {M} One, ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>8\<^sub>t = "(?\<mu>(0 := ?\<mu> 0 - 1), Some (?\<mu> 0 - 1), ?\<mu> (?\<mu> 0 - 1) - ?\<mu> (?\<mu> 0), 
      [CBAssm {M} One, ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>6\<^sub>f = "(?\<mu>(0 := ?\<mu> 0 - 1), None, ?\<mu> (?\<mu> 0 - 1) - ?\<mu> (?\<mu> 0), 
      [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} Zero, ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>7\<^sub>f = "(?\<mu>(0 := ?\<mu> 0 - 1), Some 0, ?\<mu> (?\<mu> 0 - 1) - ?\<mu> (?\<mu> 0), 
      [CBAssm {A} (Reg M), CBAssm {M} Zero, ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>8\<^sub>f = "(?\<mu>(0 := ?\<mu> 0 - 1), Some (?\<mu> 0 - 1), ?\<mu> (?\<mu> 0 - 1) - ?\<mu> (?\<mu> 0), 
      [CBAssm {M} Zero, ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>9 = "(stack_to_mem (unboolify (i2 > i1) # \<sigma>) ?\<mu>, Some (?\<mu> 0 - 1), 
      ?\<mu> (?\<mu> 0 - 1) - ?\<mu> (?\<mu> 0), [ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>1\<^sub>0 = "(stack_to_mem (unboolify (i2 > i1) # \<sigma>) ?\<mu>, Some 0, 
      ?\<mu> (?\<mu> 0 - 1) - ?\<mu> (?\<mu> 0), ?\<pi>', s, \<omega>)"
    from M have step1: "eval_b_assembly (program_convert \<Pi>) \<Sigma>\<^sub>A = Some ?\<Sigma>\<^sub>A\<^sub>1" by simp
    have step2: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>1 = Some ?\<Sigma>\<^sub>A\<^sub>2" by simp
    have step3: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>2 = Some ?\<Sigma>\<^sub>A\<^sub>3" by simp
    have step4: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>3 = Some ?\<Sigma>\<^sub>A\<^sub>4" by (simp add: Let_def)
    have step5: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>4 = Some ?\<Sigma>\<^sub>A\<^sub>5" by simp
    have step6t: "?\<mu> (?\<mu> 0 - 1) > ?\<mu> (?\<mu> 0) \<Longrightarrow> 
      eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>5 = Some ?\<Sigma>\<^sub>A\<^sub>6\<^sub>t" by simp
    have step7t: "?\<mu> (?\<mu> 0 - 1) > ?\<mu> (?\<mu> 0) \<Longrightarrow> 
      eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>6\<^sub>t = Some ?\<Sigma>\<^sub>A\<^sub>7\<^sub>t" by simp
    have step8t: "?\<mu> (?\<mu> 0 - 1) > ?\<mu> (?\<mu> 0) \<Longrightarrow> 
      eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>7\<^sub>t = Some ?\<Sigma>\<^sub>A\<^sub>8\<^sub>t" by simp
    have step9t: "?\<mu> (?\<mu> 0 - 1) > ?\<mu> (?\<mu> 0) \<Longrightarrow> 
      eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>8\<^sub>t = Some ?\<Sigma>\<^sub>A\<^sub>9" by simp
    have step6f: "\<not> ?\<mu> (?\<mu> 0 - 1) > ?\<mu> (?\<mu> 0) \<Longrightarrow> 
      eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>5 = Some ?\<Sigma>\<^sub>A\<^sub>6\<^sub>f" by simp
    have step7f: "\<not> ?\<mu> (?\<mu> 0 - 1) > ?\<mu> (?\<mu> 0) \<Longrightarrow> 
      eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>6\<^sub>f = Some ?\<Sigma>\<^sub>A\<^sub>7\<^sub>f" by simp
    have step8f: "\<not> ?\<mu> (?\<mu> 0 - 1) > ?\<mu> (?\<mu> 0) \<Longrightarrow> 
      eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>7\<^sub>f = Some ?\<Sigma>\<^sub>A\<^sub>8\<^sub>f" by simp
    have step9f: "\<not> ?\<mu> (?\<mu> 0 - 1) > ?\<mu> (?\<mu> 0) \<Longrightarrow> 
      eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>8\<^sub>f = Some ?\<Sigma>\<^sub>A\<^sub>9" by simp
    have step10: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>9 = Some ?\<Sigma>\<^sub>A\<^sub>1\<^sub>0" by simp
    from iter_two iter_prestep step1 step2 step3 have 
      "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>3" by fast
    with iter_two step4 step5 have Y: 
      "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>5" by fast
    have "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>5 ?\<Sigma>\<^sub>A\<^sub>1\<^sub>0"
      proof (cases "?\<mu> (?\<mu> 0 - 1) > ?\<mu> (?\<mu> 0)")
      case True
        with iter_two iter_prestep step6t step7t step8t have 
          "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>5 ?\<Sigma>\<^sub>A\<^sub>8\<^sub>t" by fast
        with True iter_two step9t step10 show ?thesis by fast
      next case False
        with iter_two iter_prestep step6f step7f step8f have 
          "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>5 ?\<Sigma>\<^sub>A\<^sub>8\<^sub>f" by fast
        with False iter_two step9f step10 show ?thesis by fast
      qed
    with Y iter_many have X: "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>1\<^sub>0" by fast
    have "?\<Sigma>\<^sub>A\<^sub>1\<^sub>0 \<in> state_convert (unboolify (i2 > i1) # \<sigma>, \<pi>, s, \<omega>)" by fastforce
    with X show ?case by metis
  next case (evf_lt \<Pi> i1 i2 \<sigma> \<pi> s \<omega>)
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    from evf_lt obtain d \<mu> where M: "\<Sigma>\<^sub>A = (stack_to_mem (i1 # i2 # \<sigma>) \<mu>, Some 0, d, 
      [CBAssm {A} (Reg M), CBAssm {D} (Reg M), ABAssm 0, 
       CBAssm {A, M} (Decr M), CBAssm {D} MMinusD, 
       IBAssm {LT} [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} One] 
                   [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} Zero], ABAssm 0] @ ?\<pi>', s, \<omega>)" 
      by fastforce
    let ?\<mu> = "stack_to_mem (i1 # i2 # \<sigma>) \<mu>"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(?\<mu>, Some (?\<mu> 0), d, 
      [CBAssm {D} (Reg M), ABAssm 0, CBAssm {A, M} (Decr M), CBAssm {D} MMinusD, 
       IBAssm {LT} [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} One] 
                   [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} Zero], ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(?\<mu>, Some (?\<mu> 0), ?\<mu> (?\<mu> 0), 
      [ABAssm 0, CBAssm {A, M} (Decr M), CBAssm {D} MMinusD, 
       IBAssm {LT} [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} One] 
                   [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} Zero], ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>3 = "(?\<mu>, Some 0, ?\<mu> (?\<mu> 0), 
      [CBAssm {A, M} (Decr M), CBAssm {D} MMinusD, 
       IBAssm {LT} [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} One] 
                   [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} Zero], ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>4 = "(?\<mu>(0 := ?\<mu> 0 - 1), Some (?\<mu> 0 - 1), ?\<mu> (?\<mu> 0), 
      [CBAssm {D} MMinusD, IBAssm {LT} [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} One] 
        [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} Zero], ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>5 = "(?\<mu>(0 := ?\<mu> 0 - 1), Some (?\<mu> 0 - 1), ?\<mu> (?\<mu> 0 - 1) - ?\<mu> (?\<mu> 0), 
      [IBAssm {LT} [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} One] 
                   [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} Zero], ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>6\<^sub>t = "(?\<mu>(0 := ?\<mu> 0 - 1), None, ?\<mu> (?\<mu> 0 - 1) - ?\<mu> (?\<mu> 0), 
      [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} One, ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>7\<^sub>t = "(?\<mu>(0 := ?\<mu> 0 - 1), Some 0, ?\<mu> (?\<mu> 0 - 1) - ?\<mu> (?\<mu> 0), 
      [CBAssm {A} (Reg M), CBAssm {M} One, ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>8\<^sub>t = "(?\<mu>(0 := ?\<mu> 0 - 1), Some (?\<mu> 0 - 1), ?\<mu> (?\<mu> 0 - 1) - ?\<mu> (?\<mu> 0), 
      [CBAssm {M} One, ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>6\<^sub>f = "(?\<mu>(0 := ?\<mu> 0 - 1), None, ?\<mu> (?\<mu> 0 - 1) - ?\<mu> (?\<mu> 0), 
      [ABAssm 0, CBAssm {A} (Reg M), CBAssm {M} Zero, ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>7\<^sub>f = "(?\<mu>(0 := ?\<mu> 0 - 1), Some 0, ?\<mu> (?\<mu> 0 - 1) - ?\<mu> (?\<mu> 0), 
      [CBAssm {A} (Reg M), CBAssm {M} Zero, ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>8\<^sub>f = "(?\<mu>(0 := ?\<mu> 0 - 1), Some (?\<mu> 0 - 1), ?\<mu> (?\<mu> 0 - 1) - ?\<mu> (?\<mu> 0), 
      [CBAssm {M} Zero, ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>9 = "(stack_to_mem (unboolify (i2 < i1) # \<sigma>) ?\<mu>, Some (?\<mu> 0 - 1), 
      ?\<mu> (?\<mu> 0 - 1) - ?\<mu> (?\<mu> 0), [ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>1\<^sub>0 = "(stack_to_mem (unboolify (i2 < i1) # \<sigma>) ?\<mu>, Some 0, 
      ?\<mu> (?\<mu> 0 - 1) - ?\<mu> (?\<mu> 0), ?\<pi>', s, \<omega>)"
    from M have step1: "eval_b_assembly (program_convert \<Pi>) \<Sigma>\<^sub>A = Some ?\<Sigma>\<^sub>A\<^sub>1" by simp
    have step2: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>1 = Some ?\<Sigma>\<^sub>A\<^sub>2" by simp
    have step3: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>2 = Some ?\<Sigma>\<^sub>A\<^sub>3" by simp
    have step4: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>3 = Some ?\<Sigma>\<^sub>A\<^sub>4" by (simp add: Let_def)
    have step5: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>4 = Some ?\<Sigma>\<^sub>A\<^sub>5" by simp
    have step6t: "?\<mu> (?\<mu> 0 - 1) < ?\<mu> (?\<mu> 0) \<Longrightarrow> 
      eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>5 = Some ?\<Sigma>\<^sub>A\<^sub>6\<^sub>t" by simp
    have step7t: "?\<mu> (?\<mu> 0 - 1) < ?\<mu> (?\<mu> 0) \<Longrightarrow> 
      eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>6\<^sub>t = Some ?\<Sigma>\<^sub>A\<^sub>7\<^sub>t" by simp
    have step8t: "?\<mu> (?\<mu> 0 - 1) < ?\<mu> (?\<mu> 0) \<Longrightarrow> 
      eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>7\<^sub>t = Some ?\<Sigma>\<^sub>A\<^sub>8\<^sub>t" by simp
    have step9t: "?\<mu> (?\<mu> 0 - 1) < ?\<mu> (?\<mu> 0) \<Longrightarrow> 
      eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>8\<^sub>t = Some ?\<Sigma>\<^sub>A\<^sub>9" by simp
    have step6f: "\<not> ?\<mu> (?\<mu> 0 - 1) < ?\<mu> (?\<mu> 0) \<Longrightarrow> 
      eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>5 = Some ?\<Sigma>\<^sub>A\<^sub>6\<^sub>f" by simp
    have step7f: "\<not> ?\<mu> (?\<mu> 0 - 1) < ?\<mu> (?\<mu> 0) \<Longrightarrow> 
      eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>6\<^sub>f = Some ?\<Sigma>\<^sub>A\<^sub>7\<^sub>f" by simp
    have step8f: "\<not> ?\<mu> (?\<mu> 0 - 1) < ?\<mu> (?\<mu> 0) \<Longrightarrow> 
      eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>7\<^sub>f = Some ?\<Sigma>\<^sub>A\<^sub>8\<^sub>f" by simp
    have step9f: "\<not> ?\<mu> (?\<mu> 0 - 1) < ?\<mu> (?\<mu> 0) \<Longrightarrow> 
      eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>8\<^sub>f = Some ?\<Sigma>\<^sub>A\<^sub>9" by simp
    have step10: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>9 = Some ?\<Sigma>\<^sub>A\<^sub>1\<^sub>0" by simp
    from iter_two iter_prestep step1 step2 step3 have 
      "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>3" by fast
    with iter_two step4 step5 have Y: 
      "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>5" by fast
    have "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>5 ?\<Sigma>\<^sub>A\<^sub>1\<^sub>0"
      proof (cases "?\<mu> (?\<mu> 0 - 1) < ?\<mu> (?\<mu> 0)")
      case True
        with iter_two iter_prestep step6t step7t step8t have 
          "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>5 ?\<Sigma>\<^sub>A\<^sub>8\<^sub>t" by fast
        with True iter_two step9t step10 show ?thesis by fast
      next case False
        with iter_two iter_prestep step6f step7f step8f have 
          "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>5 ?\<Sigma>\<^sub>A\<^sub>8\<^sub>f" by fast
        with False iter_two step9f step10 show ?thesis by fast
      qed
    with Y iter_many have X: "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>1\<^sub>0" by fast
    have "?\<Sigma>\<^sub>A\<^sub>1\<^sub>0 \<in> state_convert (unboolify (i2 < i1) # \<sigma>, \<pi>, s, \<omega>)" by fastforce
    with X show ?case by metis
  next case (evf_and \<Pi> i1 i2 \<sigma> \<pi> s \<omega>)
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    from evf_and obtain d \<mu> where M: "\<Sigma>\<^sub>A = (stack_to_mem (i1 # i2 # \<sigma>) \<mu>, Some 0, d, 
      [CBAssm {A} (Reg M), CBAssm {D} (Reg M), ABAssm 0, 
       CBAssm {A, M} (Decr M), CBAssm {M} DAndM, ABAssm 0] @ ?\<pi>', s, \<omega>)" by fastforce
    let ?\<mu> = "stack_to_mem (i1 # i2 # \<sigma>) \<mu>"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(?\<mu>, Some (?\<mu> 0), d, 
      [CBAssm {D} (Reg M), ABAssm 0, CBAssm {A, M} (Decr M), CBAssm {M} DAndM, ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(?\<mu>, Some (?\<mu> 0), ?\<mu> (?\<mu> 0), 
      [ABAssm 0, CBAssm {A, M} (Decr M), CBAssm {M} DAndM, ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>3 = "(?\<mu>, Some 0, ?\<mu> (?\<mu> 0), 
      [CBAssm {A, M} (Decr M), CBAssm {M} DAndM, ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>4 = "(?\<mu>(0 := ?\<mu> 0 - 1), Some (?\<mu> 0 - 1), ?\<mu> (?\<mu> 0), 
      [CBAssm {M} DAndM, ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>5 = "(stack_to_mem (unboolify (boolify i1 \<and> boolify i2) # \<sigma>) ?\<mu>, Some (?\<mu> 0 - 1), 
      ?\<mu> (?\<mu> 0), [ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>6 = "(stack_to_mem (unboolify (boolify i1 \<and> boolify i2) # \<sigma>) ?\<mu>, Some 0, 
      ?\<mu> (?\<mu> 0), ?\<pi>', s, \<omega>)"
    from M have step1: "eval_b_assembly (program_convert \<Pi>) \<Sigma>\<^sub>A = Some ?\<Sigma>\<^sub>A\<^sub>1" by simp
    have step2: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>1 = Some ?\<Sigma>\<^sub>A\<^sub>2" by simp
    have step3: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>2 = Some ?\<Sigma>\<^sub>A\<^sub>3" by simp
    have step4: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>3 = Some ?\<Sigma>\<^sub>A\<^sub>4" by (simp add: Let_def)
    have step5: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>4 = Some ?\<Sigma>\<^sub>A\<^sub>5" by simp
    have step6: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>5 = Some ?\<Sigma>\<^sub>A\<^sub>6" by simp
    from iter_two iter_prestep step1 step2 step3 have
      "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>3" by fast
    moreover from iter_two iter_prestep step4 step5 step6 have
      "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>3 ?\<Sigma>\<^sub>A\<^sub>6" by fast
    ultimately have X: "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>6" by fast
    have "?\<Sigma>\<^sub>A\<^sub>6 \<in> state_convert (unboolify (boolify i2 \<and> boolify i1) # \<sigma>, \<pi>, s, \<omega>)" by auto
    with X M show ?case by metis
  next case (evf_or \<Pi> i1 i2 \<sigma> \<pi> s \<omega>)
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    from evf_or obtain d \<mu> where M: "\<Sigma>\<^sub>A = (stack_to_mem (i1 # i2 # \<sigma>) \<mu>, Some 0, d, 
      [CBAssm {A} (Reg M), CBAssm {D} (Reg M), ABAssm 0, 
       CBAssm {A, M} (Decr M), CBAssm {M} DOrM, ABAssm 0] @ ?\<pi>', s, \<omega>)" by fastforce
    let ?\<mu> = "stack_to_mem (i1 # i2 # \<sigma>) \<mu>"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(?\<mu>, Some (?\<mu> 0), d, 
      [CBAssm {D} (Reg M), ABAssm 0, CBAssm {A, M} (Decr M), CBAssm {M} DOrM, ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(?\<mu>, Some (?\<mu> 0), ?\<mu> (?\<mu> 0), 
      [ABAssm 0, CBAssm {A, M} (Decr M), CBAssm {M} DOrM, ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>3 = "(?\<mu>, Some 0, ?\<mu> (?\<mu> 0), 
      [CBAssm {A, M} (Decr M), CBAssm {M} DOrM, ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>4 = "(?\<mu>(0 := ?\<mu> 0 - 1), Some (?\<mu> 0 - 1), ?\<mu> (?\<mu> 0), 
      [CBAssm {M} DOrM, ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>5 = "(stack_to_mem (unboolify (boolify i1 \<or> boolify i2) # \<sigma>) ?\<mu>, Some (?\<mu> 0 - 1), 
      ?\<mu> (?\<mu> 0), [ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>6 = "(stack_to_mem (unboolify (boolify i1 \<or> boolify i2) # \<sigma>) ?\<mu>, Some 0, 
      ?\<mu> (?\<mu> 0), ?\<pi>', s, \<omega>)"
    from M have step1: "eval_b_assembly (program_convert \<Pi>) \<Sigma>\<^sub>A = Some ?\<Sigma>\<^sub>A\<^sub>1" by simp
    have step2: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>1 = Some ?\<Sigma>\<^sub>A\<^sub>2" by simp
    have step3: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>2 = Some ?\<Sigma>\<^sub>A\<^sub>3" by simp
    have step4: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>3 = Some ?\<Sigma>\<^sub>A\<^sub>4" by (simp add: Let_def)
    have step5: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>4 = Some ?\<Sigma>\<^sub>A\<^sub>5" by simp
    have step6: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>5 = Some ?\<Sigma>\<^sub>A\<^sub>6" by simp
    from iter_two iter_prestep step1 step2 step3 have
      "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>3" by fast
    moreover from iter_two iter_prestep step4 step5 step6 have
      "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>3 ?\<Sigma>\<^sub>A\<^sub>6" by fast
    ultimately have X: "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>6" by fast
    have "?\<Sigma>\<^sub>A\<^sub>6 \<in> state_convert (unboolify (boolify i2 \<or> boolify i1) # \<sigma>, \<pi>, s, \<omega>)" by auto
    with X show ?case by metis
  next case (evf_not \<Pi> i1 \<sigma> \<pi> s \<omega>)
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    from evf_not obtain d \<mu> where M: "\<Sigma>\<^sub>A = (stack_to_mem (i1 # \<sigma>) \<mu>, Some 0, d, 
      [CBAssm {A} (Reg M), CBAssm {M} (NotR M), ABAssm 0] @ ?\<pi>', s, \<omega>)" by fastforce
    let ?\<mu> = "stack_to_mem (i1 # \<sigma>) \<mu>"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(?\<mu>, Some (?\<mu> 0), d, [CBAssm {M} (NotR M), ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(?\<mu>(?\<mu> 0 := unboolify (\<not> boolify (?\<mu> (?\<mu> 0)))), Some (?\<mu> 0), d, 
      [ABAssm 0] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>3 = "(?\<mu>(?\<mu> 0 := unboolify (\<not> boolify (?\<mu> (?\<mu> 0)))), Some 0, d, ?\<pi>', s, \<omega>)"
    from M have step1: "eval_b_assembly (program_convert \<Pi>) \<Sigma>\<^sub>A = Some ?\<Sigma>\<^sub>A\<^sub>1" by simp
    have step2: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>1 = Some ?\<Sigma>\<^sub>A\<^sub>2" by simp
    have "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>2 = Some ?\<Sigma>\<^sub>A\<^sub>3" by simp
    with iter_two iter_prestep step1 step2 have X:
      "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>3" by fast
    have "(stack_to_mem (i1 # \<sigma>) \<mu>)(1 + int (length \<sigma>) := unboolify (\<not> boolify i1)) = 
      stack_to_mem (unboolify (\<not> boolify i1) # \<sigma>) \<mu>" by auto
    hence "?\<Sigma>\<^sub>A\<^sub>3 \<in> state_convert (unboolify (\<not> boolify i1) # \<sigma>, \<pi>, s, \<omega>)" by auto
    with X show ?case by metis
  next case (evf_print \<Pi> i1 \<sigma> \<pi> s \<omega>)
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    from evf_print obtain d \<mu> where M: "\<Sigma>\<^sub>A = (stack_to_mem (i1 # \<sigma>) \<mu>, Some 0, d, 
        [CBAssm {A} (Reg M), CBAssm {D} (Reg M), PBAssm, ABAssm 0, CBAssm {M} (Decr M)] @ ?\<pi>', s, \<omega>)" 
      by fastforce
    let ?\<mu> = "stack_to_mem (i1 # \<sigma>) \<mu>"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(?\<mu>, Some (?\<mu> 0), d, 
      [CBAssm {D} (Reg M), PBAssm, ABAssm 0, CBAssm {M} (Decr M)] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(?\<mu>, Some (?\<mu> 0), ?\<mu> (?\<mu> 0), [PBAssm, ABAssm 0, CBAssm {M} (Decr M)] @ ?\<pi>', s, \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>3 = "(?\<mu>, Some (?\<mu> 0), ?\<mu> (?\<mu> 0), 
      [ABAssm 0, CBAssm {M} (Decr M)] @ ?\<pi>', s, ?\<mu> (?\<mu> 0) # \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>4 = "(?\<mu>, Some 0, ?\<mu> (?\<mu> 0), [CBAssm {M} (Decr M)] @ ?\<pi>', s, ?\<mu> (?\<mu> 0) # \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>5 = "(?\<mu>(0 := ?\<mu> 0 - 1), Some 0, ?\<mu> (?\<mu> 0), ?\<pi>', s, ?\<mu> (?\<mu> 0) # \<omega>)"
    from M have step1: "eval_b_assembly (program_convert \<Pi>) \<Sigma>\<^sub>A = Some ?\<Sigma>\<^sub>A\<^sub>1" by simp
    have step2: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>1 = Some ?\<Sigma>\<^sub>A\<^sub>2" by simp
    have step3: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>2 = Some ?\<Sigma>\<^sub>A\<^sub>3" by simp
    have step4: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>3 = Some ?\<Sigma>\<^sub>A\<^sub>4" by simp
    have step5: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>4 = Some ?\<Sigma>\<^sub>A\<^sub>5" by simp
    from iter_two iter_prestep step1 step2 step3 have
      "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>3" by fast
    moreover from iter_two step4 step5 have 
      "iterate (eval_b_assembly (program_convert \<Pi>)) ?\<Sigma>\<^sub>A\<^sub>3 ?\<Sigma>\<^sub>A\<^sub>5" by fast
    ultimately have X: "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>5" by fast
    have "?\<Sigma>\<^sub>A\<^sub>5 \<in> state_convert (\<sigma>, \<pi>, s, i1 # \<omega>)" by auto
    with X show ?case by metis
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