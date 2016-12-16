theory StackToAssembly
imports StackLanguage AssemblyLanguage Iterate
begin

primrec instruction_conv :: "stack_instruction \<Rightarrow> assembly list" where
  "instruction_conv Add = [AAssm 0, CAssm {A} (Reg M), CAssm {D} (Reg M), AAssm 0, CAssm {A, M} (Decr M), CAssm {M} DPlusM]"
| "instruction_conv Sub = [AAssm 0, CAssm {A} (Reg M), CAssm {D} (Reg M), AAssm 0, CAssm {A, M} (Decr M), CAssm {M} MMinusD]"
| "instruction_conv Neg = [AAssm 0, CAssm {A} (Reg M), CAssm {M} (NegR M)]"
| "instruction_conv Eq = undefined"
| "instruction_conv Gt = undefined"
| "instruction_conv Lt = undefined"
| "instruction_conv And = [AAssm 0, CAssm {A} (Reg M), CAssm {D} (Reg M), AAssm 0, CAssm {A, M} (Decr M), CAssm {M} DAndM]"
| "instruction_conv Or = [AAssm 0, CAssm {A} (Reg M), CAssm {D} (Reg M), AAssm 0, CAssm {A, M} (Decr M), CAssm {M} DOrM]"
| "instruction_conv Not = [AAssm 0, CAssm {A} (Reg M), CAssm {D} (NotR M)]"

definition program_convert :: "stack_program \<Rightarrow> assembly_program" where
  "program_convert \<Pi> = map_option concat o map_option (map instruction_conv) o \<Pi>"

primrec stack_to_mem :: "int list \<Rightarrow> (int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int" where
  "stack_to_mem [] \<mu> k = \<mu> k"
| "stack_to_mem (i # is) \<mu> k = (if k > 0 \<and> nat k = Suc (length is) then i else stack_to_mem is \<mu> k)" 

primrec state_convert :: "stack_state \<Rightarrow> assembly_state set" where
  "state_convert (\<sigma>, \<pi>) = {((stack_to_mem \<sigma> \<mu>)(0 := int (length \<sigma>)), None, d, concat (map instruction_conv \<pi>)) | d \<mu>. True }"

(* conversion correctness *)

lemma [simp]: "dom (program_convert \<Pi>) = dom \<Pi>"
  by (auto simp add: program_convert_def)

lemma eval_stack_conv [simp]: "eval_stack \<Pi> \<Sigma>\<^sub>S = Some \<Sigma>\<^sub>S' \<Longrightarrow> \<Sigma>\<^sub>A \<in> state_convert \<Sigma>\<^sub>S \<Longrightarrow> 
    \<exists>\<Sigma>\<^sub>A'. \<Sigma>\<^sub>A' \<in> state_convert \<Sigma>\<^sub>S' \<and> iterate (eval_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A \<Sigma>\<^sub>A'"
  proof (induction \<Pi> \<Sigma>\<^sub>S rule: eval_stack.induct)
  case (1 \<Pi> i1 i2 \<sigma> \<pi>)
    then obtain d \<mu> where M: "\<Sigma>\<^sub>A = ((stack_to_mem (i1 # i2 # \<sigma>) \<mu>)(0 :=  int (Suc (Suc (length \<sigma>)))), None, d, concat (map instruction_conv (Add # \<pi>)))" by fastforce
    from 1 have S: "\<Sigma>\<^sub>S' = ((i2 + i1) # \<sigma>, \<pi>)" by simp

    let ?ev = "eval_assembly (program_convert \<Pi>)"
    let ?\<mu>' = "(stack_to_mem (i1 # i2 # \<sigma>) \<mu>)(0 :=  int (Suc (Suc (length \<sigma>))))"

    have step1: "?ev (?\<mu>', None, d, [AAssm 0, CAssm {A} (Reg M), CAssm {D} (Reg M), AAssm 0, CAssm {A, M} (Decr M), CAssm {M} DPlusM] @ concat (map instruction_conv \<pi>)) = 
      Some (?\<mu>', Some 0, d, [CAssm {A} (Reg M), CAssm {D} (Reg M), AAssm 0, CAssm {A, M} (Decr M), CAssm {M} DPlusM] @ concat (map instruction_conv \<pi>))" by simp
    have step2: "?ev (?\<mu>', Some 0, d, [CAssm {A} (Reg M), CAssm {D} (Reg M), AAssm 0, CAssm {A, M} (Decr M), CAssm {M} DPlusM] @ concat (map instruction_conv \<pi>)) = 
      Some (?\<mu>', Some (?\<mu>' 0), d, [CAssm {D} (Reg M), AAssm 0, CAssm {A, M} (Decr M), CAssm {M} DPlusM] @ concat (map instruction_conv \<pi>))" by simp
    have step3: "?ev (?\<mu>', Some (?\<mu>' 0), d, [CAssm {D} (Reg M), AAssm 0, CAssm {A, M} (Decr M), CAssm {M} DPlusM] @ concat (map instruction_conv \<pi>)) = 
      Some (?\<mu>', Some (?\<mu>' 0), ?\<mu>' (?\<mu>' 0), [AAssm 0, CAssm {A, M} (Decr M), CAssm {M} DPlusM] @ concat (map instruction_conv \<pi>))" by simp
    have step4: "?ev (?\<mu>', Some (?\<mu>' 0), ?\<mu>' (?\<mu>' 0), [AAssm 0, CAssm {A, M} (Decr M), CAssm {M} DPlusM] @ concat (map instruction_conv \<pi>)) = 
      Some (?\<mu>', Some 0, ?\<mu>' (?\<mu>' 0), [CAssm {A, M} (Decr M), CAssm {M} DPlusM] @ concat (map instruction_conv \<pi>))" by simp
    have step5: "?ev (?\<mu>', Some 0, ?\<mu>' (?\<mu>' 0), [CAssm {A, M} (Decr M), CAssm {M} DPlusM] @ concat (map instruction_conv \<pi>)) = 
      Some (?\<mu>'(0 := ?\<mu>' 0 - 1), Some (?\<mu>' 0 - 1), ?\<mu>' (?\<mu>' 0), [CAssm {M} DPlusM] @ concat (map instruction_conv \<pi>))" by simp
    have step6: "?ev (?\<mu>'(0 := ?\<mu>' 0 - 1), Some (?\<mu>' 0 - 1), ?\<mu>' (?\<mu>' 0), [CAssm {M} DPlusM] @ concat (map instruction_conv \<pi>)) = 
      Some (?\<mu>'(0 := ?\<mu>' 0 - 1, ?\<mu>' 0 - 1 := ?\<mu>' (?\<mu>' 0) + ?\<mu>' (?\<mu>' 0 - 1)), Some (?\<mu>' 0 - 1), ?\<mu>' (?\<mu>' 0), concat (map instruction_conv \<pi>))" by simp



    have "\<Sigma>\<^sub>A' \<in> state_convert ((i2 + i1) # \<sigma>, \<pi>) \<and> iterate ?ev (?\<mu>', None, d, [AAssm 0, CAssm {A} (Reg M), CAssm {D} (Reg M), AAssm 0, CAssm {A, M} (Decr M), CAssm {M} DPlusM] @ concat (map instruction_conv \<pi>)) \<Sigma>\<^sub>A'" by simp
    hence "\<Sigma>\<^sub>A' \<in> state_convert ((i2 + i1) # \<sigma>, \<pi>) \<and> iterate ?ev (?\<mu>', None, d, concat (map instruction_conv (Add # \<pi>))) \<Sigma>\<^sub>A'" by simp
    with S M show ?case by blast
  next case 2
    thus ?case by simp
  next case 3
    thus ?case by simp
  next case 4
    thus ?case by simp
  next case 5
    thus ?case by simp
  next case 6
    thus ?case by simp
  next case 7
    thus ?case by simp
  next case 8
    thus ?case by simp
  next case 9
    thus ?case by simp

  (* autogenerated cases where "eval_stack \<Pi> \<Sigma>\<^sub>S = None" *)
  next case "10_1" thus ?case by simp
  next case "10_2" thus ?case by simp
  next case "10_3" thus ?case by simp
  next case "10_4" thus ?case by simp
  next case "10_5" thus ?case by simp
  next case "10_6" thus ?case by simp
  next case "10_7" thus ?case by simp
  next case "10_8" thus ?case by simp
  next case "10_9" thus ?case by simp
  next case "10_10" thus ?case by simp
  next case "10_11" thus ?case by simp
  next case "10_12" thus ?case by simp
  next case "10_13" thus ?case by simp
  next case "10_14" thus ?case by simp
  next case "10_15" thus ?case by simp
  next case "10_16" thus ?case by simp
  next case "10_17" thus ?case by simp
  next case "10_18" thus ?case by simp
  next case "10_19" thus ?case by simp
  next case "10_20" thus ?case by simp
  next case "10_21" thus ?case by simp
  next case "10_22" thus ?case by simp
  next case "10_23" thus ?case by simp
  next case "10_24" thus ?case by simp
  qed

theorem stack_to_assembly_correct [simp]: "iterate (eval_stack \<Pi>) \<Sigma>\<^sub>S \<Sigma>\<^sub>S' \<Longrightarrow> 
  \<Sigma>\<^sub>A \<in> state_convert \<Sigma>\<^sub>S \<Longrightarrow> 
    \<exists>\<Sigma>\<^sub>A'. \<Sigma>\<^sub>A' \<in> state_convert \<Sigma>\<^sub>S' \<and> iterate (eval_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A \<Sigma>\<^sub>A'"
  proof (induction "eval_stack \<Pi>" \<Sigma>\<^sub>S \<Sigma>\<^sub>S' arbitrary: \<Sigma>\<^sub>A rule: iterate.induct)
  case iter_refl
    thus ?case by fastforce
  next case (iter_step \<Sigma>\<^sub>S \<Sigma>\<^sub>S' \<Sigma>\<^sub>S'')
    then obtain \<Sigma>\<^sub>A' where S: "\<Sigma>\<^sub>A' \<in> state_convert \<Sigma>\<^sub>S' \<and> 
      iterate (eval_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A \<Sigma>\<^sub>A'" by blast
    with iter_step eval_stack_conv obtain \<Sigma>\<^sub>A'' where
        "\<Sigma>\<^sub>A'' \<in> state_convert \<Sigma>\<^sub>S'' \<and> iterate (eval_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A' \<Sigma>\<^sub>A''" 
      by blast
    with S have "\<Sigma>\<^sub>A'' \<in> state_convert \<Sigma>\<^sub>S'' \<and> 
      iterate (eval_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A \<Sigma>\<^sub>A''" by fastforce
    thus ?case by blast
  qed

end