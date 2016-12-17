theory StackToAssembly
imports StackLanguage BranchingAssemblyLanguage Iterate
begin

primrec instruction_conv :: "stack_instruction \<Rightarrow> b_assembly list" where
  "instruction_conv Add = [
    CBAssm {A} (Reg M), 
    CBAssm {D} (Reg M), 
    ABAssm 0, 
    CBAssm {A, M} (Decr M), 
    CBAssm {M} DPlusM, 
    ABAssm 0]"
| "instruction_conv Sub = [
    CBAssm {A} (Reg M),
    CBAssm {D} (Reg M), 
    ABAssm 0, 
    CBAssm {A, M} (Decr M), 
    CBAssm {M} MMinusD, 
    ABAssm 0]"
| "instruction_conv Neg = [
    CBAssm {A} (Reg M), 
    CBAssm {M} (NegR M), 
    ABAssm 0]"
| "instruction_conv Eq = undefined"
| "instruction_conv Gt = undefined"
| "instruction_conv Lt = undefined"
| "instruction_conv And = [
    CBAssm {A} (Reg M), 
    CBAssm {D} (Reg M), 
    ABAssm 0, 
    CBAssm {A, M} (Decr M), 
    CBAssm {M} DAndM, 
    ABAssm 0]"
| "instruction_conv Or = [
    CBAssm {A} (Reg M), 
    CBAssm {D} (Reg M), 
    ABAssm 0, 
    CBAssm {A, M} (Decr M), 
    CBAssm {M} DOrM, 
    ABAssm 0]"
| "instruction_conv Not = [
    CBAssm {A} (Reg M), 
    CBAssm {M} (NotR M), 
    ABAssm 0]"
| "instruction_conv Print = [
    CBAssm {A} (Reg M), 
    CBAssm {D} (Reg M),
    PBAssm,
    ABAssm 0, 
    CBAssm {M} (Decr M)]"

definition program_convert :: "stack_program \<Rightarrow> b_assembly_program" where
  "program_convert \<Pi> = map_option concat o map_option (map instruction_conv) o \<Pi>"

primrec stack_to_mem :: "int list \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int" where
  "stack_to_mem [] \<mu> k = (if k = 0 then 0 else \<mu> k)"
| "stack_to_mem (i # is) \<mu> k = (
    if k = 0 then 1 + int (length is)
    else if k = 1 + int (length is) then i
    else stack_to_mem is \<mu> k)"

fun state_convert :: "stack_state \<Rightarrow> b_assembly_state set" where
  "state_convert (\<sigma>, \<pi>, \<omega>) = 
    {(stack_to_mem \<sigma> \<mu>, Some 0, d, concat (map instruction_conv \<pi>), \<omega>) | d \<mu>. True }"

(* conversion correctness *)

lemma [simp]: "dom (program_convert \<Pi>) = dom \<Pi>"
  by (auto simp add: program_convert_def)

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

lemma [simp]: "\<Sigma>\<^sub>B \<in> state_convert \<Sigma>\<^sub>S \<Longrightarrow> b_assembly_output \<Sigma>\<^sub>B = stack_output \<Sigma>\<^sub>S"
  by (induction \<Sigma>\<^sub>S rule: stack_output.induct, induction \<Sigma>\<^sub>B rule: b_assembly_output.induct) simp

lemma eval_stack_conv [simp]: "eval_stack \<Pi> \<Sigma>\<^sub>S = Some \<Sigma>\<^sub>S' \<Longrightarrow> \<Sigma>\<^sub>A \<in> state_convert \<Sigma>\<^sub>S \<Longrightarrow> 
    \<exists>\<Sigma>\<^sub>A'. \<Sigma>\<^sub>A' \<in> state_convert \<Sigma>\<^sub>S' \<and> iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A \<Sigma>\<^sub>A'"
  proof (induction \<Pi> \<Sigma>\<^sub>S rule: eval_stack.induct)
  case (1 \<Pi> i1 i2 \<sigma> \<pi> \<omega>)
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    from 1 obtain d \<mu> where M: "\<Sigma>\<^sub>A = (stack_to_mem (i1 # i2 # \<sigma>) \<mu>, Some 0, d, 
      [CBAssm {A} (Reg M), CBAssm {D} (Reg M), ABAssm 0, 
       CBAssm {A, M} (Decr M), CBAssm {M} DPlusM, ABAssm 0] @ ?\<pi>', \<omega>)" by fastforce
    from 1 have S: "\<Sigma>\<^sub>S' = ((i1 + i2) # \<sigma>, \<pi>, \<omega>)" by auto
    let ?\<mu> = "stack_to_mem (i1 # i2 # \<sigma>) \<mu>"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(?\<mu>, Some (?\<mu> 0), d, 
      [CBAssm {D} (Reg M), ABAssm 0, CBAssm {A, M} (Decr M), CBAssm {M} DPlusM, ABAssm 0] @ ?\<pi>', \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(?\<mu>, Some (?\<mu> 0), ?\<mu> (?\<mu> 0), 
      [ABAssm 0, CBAssm {A, M} (Decr M), CBAssm {M} DPlusM, ABAssm 0] @ ?\<pi>', \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>3 = "(?\<mu>, Some 0, ?\<mu> (?\<mu> 0), 
      [CBAssm {A, M} (Decr M), CBAssm {M} DPlusM, ABAssm 0] @ ?\<pi>', \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>4 = "(?\<mu>(0 := ?\<mu> 0 - 1), Some (?\<mu> 0 - 1), ?\<mu> (?\<mu> 0), 
      [CBAssm {M} DPlusM, ABAssm 0] @ ?\<pi>', \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>5 = "(stack_to_mem ((i1 + i2) # \<sigma>) ?\<mu>, Some (?\<mu> 0 - 1), ?\<mu> (?\<mu> 0), [ABAssm 0] @ ?\<pi>', \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>6 = "(stack_to_mem ((i1 + i2) # \<sigma>) ?\<mu>, Some 0, ?\<mu> (?\<mu> 0), ?\<pi>', \<omega>)"
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
    have "?\<Sigma>\<^sub>A\<^sub>6 \<in> state_convert ((i1 + i2) # \<sigma>, \<pi>, \<omega>)" by auto
    with X S M show ?case by metis
  next case (2 \<Pi> i1 i2 \<sigma> \<pi> \<omega>)
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    from 2 obtain d \<mu> where M: "\<Sigma>\<^sub>A = (stack_to_mem (i1 # i2 # \<sigma>) \<mu>, Some 0, d, 
      [CBAssm {A} (Reg M), CBAssm {D} (Reg M), ABAssm 0, 
       CBAssm {A, M} (Decr M), CBAssm {M} MMinusD, ABAssm 0] @ ?\<pi>', \<omega>)" by fastforce
    from 2 have S: "\<Sigma>\<^sub>S' = ((i2 - i1) # \<sigma>, \<pi>, \<omega>)" by simp
    let ?\<mu> = "stack_to_mem (i1 # i2 # \<sigma>) \<mu>"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(?\<mu>, Some (?\<mu> 0), d, 
      [CBAssm {D} (Reg M), ABAssm 0, CBAssm {A, M} (Decr M), CBAssm {M} MMinusD, ABAssm 0] @ ?\<pi>', \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(?\<mu>, Some (?\<mu> 0), ?\<mu> (?\<mu> 0), 
      [ABAssm 0, CBAssm {A, M} (Decr M), CBAssm {M} MMinusD, ABAssm 0] @ ?\<pi>', \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>3 = "(?\<mu>, Some 0, ?\<mu> (?\<mu> 0), 
      [CBAssm {A, M} (Decr M), CBAssm {M} MMinusD, ABAssm 0] @ ?\<pi>', \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>4 = "(?\<mu>(0 := ?\<mu> 0 - 1), Some (?\<mu> 0 - 1), ?\<mu> (?\<mu> 0),
      [CBAssm {M} MMinusD, ABAssm 0] @ ?\<pi>', \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>5 = "(stack_to_mem ((i2 - i1) # \<sigma>) ?\<mu>, Some (?\<mu> 0 - 1), ?\<mu> (?\<mu> 0), [ABAssm 0] @ ?\<pi>', \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>6 = "(stack_to_mem ((i2 - i1) # \<sigma>) ?\<mu>, Some 0, ?\<mu> (?\<mu> 0), ?\<pi>', \<omega>)"
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
    have "?\<Sigma>\<^sub>A\<^sub>6 \<in> state_convert ((i2 - i1) # \<sigma>, \<pi>, \<omega>)" by auto
    with X S M show ?case by metis
  next case (3 \<Pi> i1 \<sigma> \<pi> \<omega>)
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    from 3 obtain d \<mu> where M: "\<Sigma>\<^sub>A = (stack_to_mem (i1 # \<sigma>) \<mu>, Some 0, d, 
      [CBAssm {A} (Reg M), CBAssm {M} (NegR M), ABAssm 0] @ ?\<pi>', \<omega>)" by fastforce
    from 3 have S: "\<Sigma>\<^sub>S' = (-i1 # \<sigma>, \<pi>, \<omega>)" by simp
    let ?\<mu> = "stack_to_mem (i1 # \<sigma>) \<mu>"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(?\<mu>, Some (?\<mu> 0), d, [CBAssm {M} (NegR M), ABAssm 0] @ ?\<pi>', \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(?\<mu>(?\<mu> 0 := - ?\<mu> (?\<mu> 0)), Some (?\<mu> 0), d, [ABAssm 0] @ ?\<pi>', \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>3 = "(?\<mu>(?\<mu> 0 := - ?\<mu> (?\<mu> 0)), Some 0, d, ?\<pi>', \<omega>)"
    from M have step1: "eval_b_assembly (program_convert \<Pi>) \<Sigma>\<^sub>A = Some ?\<Sigma>\<^sub>A\<^sub>1" by simp
    have step2: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>1 = Some ?\<Sigma>\<^sub>A\<^sub>2" by simp
    have "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>2 = Some ?\<Sigma>\<^sub>A\<^sub>3" by simp
    with iter_two iter_prestep step1 step2 have X:
      "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>3" by fast
    have "(stack_to_mem (i1 # \<sigma>) \<mu>)(1 + int (length \<sigma>) := - i1) = stack_to_mem (- i1 # \<sigma>) \<mu>" by auto
    hence "?\<Sigma>\<^sub>A\<^sub>3 \<in> state_convert ((-i1) # \<sigma>, \<pi>, \<omega>)" by auto
    with X S M show ?case by metis
  next case (4 \<Pi> i1 i2 \<sigma> \<pi> \<omega>)
    thus ?case by simp
  next case 5
    thus ?case by simp
  next case 6
    thus ?case by simp
  next case (7 \<Pi> i1 i2 \<sigma> \<pi> \<omega>)
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    from 7 obtain d \<mu> where M: "\<Sigma>\<^sub>A = (stack_to_mem (i1 # i2 # \<sigma>) \<mu>, Some 0, d, 
      [CBAssm {A} (Reg M), CBAssm {D} (Reg M), ABAssm 0, 
       CBAssm {A, M} (Decr M), CBAssm {M} DAndM, ABAssm 0] @ ?\<pi>', \<omega>)" by fastforce
    from 7 have S: "\<Sigma>\<^sub>S' = (unboolify (boolify i1 \<and> boolify i2) # \<sigma>, \<pi>, \<omega>)" by simp
    let ?\<mu> = "stack_to_mem (i1 # i2 # \<sigma>) \<mu>"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(?\<mu>, Some (?\<mu> 0), d, 
      [CBAssm {D} (Reg M), ABAssm 0, CBAssm {A, M} (Decr M), CBAssm {M} DAndM, ABAssm 0] @ ?\<pi>', \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(?\<mu>, Some (?\<mu> 0), ?\<mu> (?\<mu> 0), 
      [ABAssm 0, CBAssm {A, M} (Decr M), CBAssm {M} DAndM, ABAssm 0] @ ?\<pi>', \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>3 = "(?\<mu>, Some 0, ?\<mu> (?\<mu> 0), 
      [CBAssm {A, M} (Decr M), CBAssm {M} DAndM, ABAssm 0] @ ?\<pi>', \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>4 = "(?\<mu>(0 := ?\<mu> 0 - 1), Some (?\<mu> 0 - 1), ?\<mu> (?\<mu> 0), 
      [CBAssm {M} DAndM, ABAssm 0] @ ?\<pi>', \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>5 = "(stack_to_mem (unboolify (boolify i1 \<and> boolify i2) # \<sigma>) ?\<mu>, Some (?\<mu> 0 - 1), 
      ?\<mu> (?\<mu> 0), [ABAssm 0] @ ?\<pi>', \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>6 = "(stack_to_mem (unboolify (boolify i1 \<and> boolify i2) # \<sigma>) ?\<mu>, Some 0, 
      ?\<mu> (?\<mu> 0), ?\<pi>', \<omega>)"
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
    have "?\<Sigma>\<^sub>A\<^sub>6 \<in> state_convert (unboolify (boolify i1 \<and> boolify i2) # \<sigma>, \<pi>, \<omega>)" by auto
    with X S M show ?case by metis
  next case (8 \<Pi> i1 i2 \<sigma> \<pi> \<omega>)
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    from 8 obtain d \<mu> where M: "\<Sigma>\<^sub>A = (stack_to_mem (i1 # i2 # \<sigma>) \<mu>, Some 0, d, 
      [CBAssm {A} (Reg M), CBAssm {D} (Reg M), ABAssm 0, 
       CBAssm {A, M} (Decr M), CBAssm {M} DOrM, ABAssm 0] @ ?\<pi>', \<omega>)" by fastforce
    from 8 have S: "\<Sigma>\<^sub>S' = (unboolify (boolify i1 \<or> boolify i2) # \<sigma>, \<pi>, \<omega>)" by simp
    let ?\<mu> = "stack_to_mem (i1 # i2 # \<sigma>) \<mu>"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(?\<mu>, Some (?\<mu> 0), d, 
      [CBAssm {D} (Reg M), ABAssm 0, CBAssm {A, M} (Decr M), CBAssm {M} DOrM, ABAssm 0] @ ?\<pi>', \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(?\<mu>, Some (?\<mu> 0), ?\<mu> (?\<mu> 0), 
      [ABAssm 0, CBAssm {A, M} (Decr M), CBAssm {M} DOrM, ABAssm 0] @ ?\<pi>', \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>3 = "(?\<mu>, Some 0, ?\<mu> (?\<mu> 0), 
      [CBAssm {A, M} (Decr M), CBAssm {M} DOrM, ABAssm 0] @ ?\<pi>', \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>4 = "(?\<mu>(0 := ?\<mu> 0 - 1), Some (?\<mu> 0 - 1), ?\<mu> (?\<mu> 0), 
      [CBAssm {M} DOrM, ABAssm 0] @ ?\<pi>', \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>5 = "(stack_to_mem (unboolify (boolify i1 \<or> boolify i2) # \<sigma>) ?\<mu>, Some (?\<mu> 0 - 1), 
      ?\<mu> (?\<mu> 0), [ABAssm 0] @ ?\<pi>', \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>6 = "(stack_to_mem (unboolify (boolify i1 \<or> boolify i2) # \<sigma>) ?\<mu>, Some 0, 
      ?\<mu> (?\<mu> 0), ?\<pi>', \<omega>)"
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
    have "?\<Sigma>\<^sub>A\<^sub>6 \<in> state_convert (unboolify (boolify i1 \<or> boolify i2) # \<sigma>, \<pi>, \<omega>)" by auto
    with X S M show ?case by metis
  next case (9 \<Pi> i1 \<sigma> \<pi> \<omega>)
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    from 9 obtain d \<mu> where M: "\<Sigma>\<^sub>A = (stack_to_mem (i1 # \<sigma>) \<mu>, Some 0, d, 
      [CBAssm {A} (Reg M), CBAssm {M} (NotR M), ABAssm 0] @ ?\<pi>', \<omega>)" by fastforce
    from 9 have S: "\<Sigma>\<^sub>S' = (unboolify (\<not> boolify i1) # \<sigma>, \<pi>, \<omega>)" by simp
    let ?\<mu> = "stack_to_mem (i1 # \<sigma>) \<mu>"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(?\<mu>, Some (?\<mu> 0), d, [CBAssm {M} (NotR M), ABAssm 0] @ ?\<pi>', \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(?\<mu>(?\<mu> 0 := unboolify (\<not> boolify (?\<mu> (?\<mu> 0)))), Some (?\<mu> 0), d, 
      [ABAssm 0] @ ?\<pi>', \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>3 = "(?\<mu>(?\<mu> 0 := unboolify (\<not> boolify (?\<mu> (?\<mu> 0)))), Some 0, d, ?\<pi>', \<omega>)"
    from M have step1: "eval_b_assembly (program_convert \<Pi>) \<Sigma>\<^sub>A = Some ?\<Sigma>\<^sub>A\<^sub>1" by simp
    have step2: "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>1 = Some ?\<Sigma>\<^sub>A\<^sub>2" by simp
    have "eval_b_assembly (program_convert \<Pi>) ?\<Sigma>\<^sub>A\<^sub>2 = Some ?\<Sigma>\<^sub>A\<^sub>3" by simp
    with iter_two iter_prestep step1 step2 have X:
      "iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A ?\<Sigma>\<^sub>A\<^sub>3" by fast
    have "(stack_to_mem (i1 # \<sigma>) \<mu>)(1 + int (length \<sigma>) := unboolify (\<not> boolify i1)) = 
      stack_to_mem (unboolify (\<not> boolify i1) # \<sigma>) \<mu>" by auto
    hence "?\<Sigma>\<^sub>A\<^sub>3 \<in> state_convert (unboolify (\<not> boolify i1) # \<sigma>, \<pi>, \<omega>)" by auto
    with X S M show ?case by metis
  next case (10 \<Pi> i1 \<sigma> \<pi> \<omega>)
    let ?\<pi>' = "concat (map instruction_conv \<pi>)"
    from 10 have S: "\<Sigma>\<^sub>S' = (\<sigma>, \<pi>, i1 # \<omega>)" by simp
    from 10 obtain d \<mu> where M: "\<Sigma>\<^sub>A = (stack_to_mem (i1 # \<sigma>) \<mu>, Some 0, d, 
        [CBAssm {A} (Reg M), CBAssm {D} (Reg M), PBAssm, ABAssm 0, CBAssm {M} (Decr M)] @ ?\<pi>', \<omega>)" 
      by fastforce
    let ?\<mu> = "stack_to_mem (i1 # \<sigma>) \<mu>"
    let ?\<Sigma>\<^sub>A\<^sub>1 = "(?\<mu>, Some (?\<mu> 0), d, 
      [CBAssm {D} (Reg M), PBAssm, ABAssm 0, CBAssm {M} (Decr M)] @ ?\<pi>', \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>2 = "(?\<mu>, Some (?\<mu> 0), ?\<mu> (?\<mu> 0), [PBAssm, ABAssm 0, CBAssm {M} (Decr M)] @ ?\<pi>', \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>3 = "(?\<mu>, Some (?\<mu> 0), ?\<mu> (?\<mu> 0), [ABAssm 0, CBAssm {M} (Decr M)] @ ?\<pi>', ?\<mu> (?\<mu> 0) # \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>4 = "(?\<mu>, Some 0, ?\<mu> (?\<mu> 0), [CBAssm {M} (Decr M)] @ ?\<pi>', ?\<mu> (?\<mu> 0) # \<omega>)"
    let ?\<Sigma>\<^sub>A\<^sub>5 = "(?\<mu>(0 := ?\<mu> 0 - 1), Some 0, ?\<mu> (?\<mu> 0), ?\<pi>', ?\<mu> (?\<mu> 0) # \<omega>)"
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
    have "?\<Sigma>\<^sub>A\<^sub>5 \<in> state_convert (\<sigma>, \<pi>, i1 # \<omega>)" by auto
    with X S M show ?case by metis
  next

  (* autogenerated cases where "eval_stack \<Pi> \<Sigma>\<^sub>S = None" *)
  case "11_1" thus ?case by simp
  next case "11_2" thus ?case by simp
  next case "11_3" thus ?case by simp
  next case "11_4" thus ?case by simp
  next case "11_5" thus ?case by simp
  next case "11_6" thus ?case by simp
  next case "11_7" thus ?case by simp
  next case "11_8" thus ?case by simp
  next case "11_9" thus ?case by simp
  next case "11_10" thus ?case by simp
  next case "11_11" thus ?case by simp
  next case "11_12" thus ?case by simp
  next case "11_13" thus ?case by simp
  next case "11_14" thus ?case by simp
  next case "11_15" thus ?case by simp
  next case "11_16" thus ?case by simp
  next case "11_17" thus ?case by simp
  next case "11_18" thus ?case by simp
  next case "11_19" thus ?case by simp
  next case "11_20" thus ?case by simp
  next case "11_21" thus ?case by simp
  next case "11_22" thus ?case by simp
  next case "11_23" thus ?case by simp
  next case "11_24" thus ?case by simp
  next case "11_25" thus ?case by simp
  qed

theorem stack_to_assembly_correct [simp]: "iterate (eval_stack \<Pi>) \<Sigma>\<^sub>S \<Sigma>\<^sub>S' \<Longrightarrow> 
  \<Sigma>\<^sub>B \<in> state_convert \<Sigma>\<^sub>S \<Longrightarrow> 
    \<exists>\<Sigma>\<^sub>B'. \<Sigma>\<^sub>B' \<in> state_convert \<Sigma>\<^sub>S' \<and> iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>B \<Sigma>\<^sub>B'"
  proof (induction "eval_stack \<Pi>" \<Sigma>\<^sub>S \<Sigma>\<^sub>S' arbitrary: \<Sigma>\<^sub>B rule: iterate.induct)
  case iter_refl
    thus ?case by fastforce
  next case (iter_step \<Sigma>\<^sub>S \<Sigma>\<^sub>S' \<Sigma>\<^sub>S'')
    then obtain \<Sigma>\<^sub>B' where S: "\<Sigma>\<^sub>B' \<in> state_convert \<Sigma>\<^sub>S' \<and> 
      iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>B \<Sigma>\<^sub>B'" by blast
    with iter_step eval_stack_conv obtain \<Sigma>\<^sub>B'' where
        "\<Sigma>\<^sub>B'' \<in> state_convert \<Sigma>\<^sub>S'' \<and> iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>B' \<Sigma>\<^sub>B''" 
      by blast
    with S have "\<Sigma>\<^sub>B'' \<in> state_convert \<Sigma>\<^sub>S'' \<and> iterate (eval_b_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>B \<Sigma>\<^sub>B''" 
      by fastforce
    thus ?case by blast
  qed

end