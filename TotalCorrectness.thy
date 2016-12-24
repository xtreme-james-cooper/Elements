theory TotalCorrectness
imports 
  "LinearAssembly/AssemblyToMachine" 
  "Assembly/Linearization" 
  "BranchingAssembly/Debranching" 
  "FlatStack/StackToAssembly"
  "Stack/Flattening"
begin

definition state_convert :: "stack_program \<Rightarrow> stack_state \<Rightarrow> machine_state set" where
  "state_convert \<Pi> \<Sigma>\<^sub>S = { \<Sigma>\<^sub>M | \<Sigma>\<^sub>B \<Sigma>\<^sub>M. 
    \<Sigma>\<^sub>B \<in> StackToAssembly.state_convert (Flattening.state_convert \<Sigma>\<^sub>S) \<and> 
      \<Sigma>\<^sub>M \<in> AssemblyToMachine.state_convert
        (linearize (debranch (StackToAssembly.program_convert (flatten \<Pi>)))) 
          (Linearization.state_convert 
            (Debranching.state_convert (dom (StackToAssembly.program_convert (flatten \<Pi>))) \<Sigma>\<^sub>B)) }"

definition program_convert :: "stack_program \<Rightarrow> machine_program" where
  "program_convert = 
    AssemblyToMachine.program_convert o linearize o 
      debranch o StackToAssembly.program_convert o flatten"

theorem output_equivalence: "\<Sigma>\<^sub>M \<in> state_convert \<Pi> \<Sigma>\<^sub>S \<Longrightarrow> machine_output \<Sigma>\<^sub>M = stack_output \<Sigma>\<^sub>S"
  proof -
    let ?\<Pi>\<^sub>B = "StackToAssembly.program_convert (flatten \<Pi>)"
    let ?\<Pi>\<^sub>A = "linearize (debranch ?\<Pi>\<^sub>B)"
    assume "\<Sigma>\<^sub>M \<in> state_convert \<Pi> \<Sigma>\<^sub>S"
    with state_convert_def obtain \<Sigma>\<^sub>B where B: "
      \<Sigma>\<^sub>B \<in> StackToAssembly.state_convert (Flattening.state_convert \<Sigma>\<^sub>S) \<and> 
        \<Sigma>\<^sub>M \<in> AssemblyToMachine.state_convert ?\<Pi>\<^sub>A (Linearization.state_convert 
          (Debranching.state_convert (dom ?\<Pi>\<^sub>B) \<Sigma>\<^sub>B))" by blast
    thus ?thesis by auto
  qed

theorem total_correctness: "finite (dom \<Pi>) \<Longrightarrow> valid_state \<Pi> \<Sigma>\<^sub>S \<Longrightarrow> 
  iterate_ind (eval_stack \<Pi>) \<Sigma>\<^sub>S \<Sigma>\<^sub>S' \<Longrightarrow> \<Sigma>\<^sub>M \<in> state_convert \<Pi> \<Sigma>\<^sub>S \<Longrightarrow> 
    \<exists>\<Sigma>\<^sub>M'. \<Sigma>\<^sub>M' \<in> state_convert \<Pi> \<Sigma>\<^sub>S' \<and> iterate (eval_machine (program_convert \<Pi>)) \<Sigma>\<^sub>M \<Sigma>\<^sub>M'"
  proof -
    assume D: "finite (dom \<Pi>)"
    hence DA: "finite (dom (StackToAssembly.program_convert (flatten \<Pi>)))" by simp
    hence DF: "finite (dom (debranch (StackToAssembly.program_convert (flatten \<Pi>))))" by simp
    hence DL: "domain_distinct (linearize (debranch (StackToAssembly.program_convert (flatten \<Pi>))))" 
      by simp
    assume ES: "iterate_ind (eval_stack \<Pi>) \<Sigma>\<^sub>S \<Sigma>\<^sub>S'"
    let ?\<Pi>\<^sub>B = "StackToAssembly.program_convert (flatten \<Pi>)"
    let ?\<Pi>\<^sub>A = "debranch ?\<Pi>\<^sub>B"
    let ?\<Pi>\<^sub>M = "AssemblyToMachine.program_convert (linearize ?\<Pi>\<^sub>A)"
    assume "\<Sigma>\<^sub>M \<in> state_convert \<Pi> \<Sigma>\<^sub>S"
    with state_convert_def obtain \<Sigma>\<^sub>B where B: 
      "\<Sigma>\<^sub>B \<in> StackToAssembly.state_convert (Flattening.state_convert \<Sigma>\<^sub>S) \<and> 
        \<Sigma>\<^sub>M \<in> AssemblyToMachine.state_convert (linearize ?\<Pi>\<^sub>A) 
          (Linearization.state_convert (Debranching.state_convert (dom ?\<Pi>\<^sub>B) \<Sigma>\<^sub>B))" 
      by blast
    assume "valid_state \<Pi> \<Sigma>\<^sub>S"
    with ES B stack_to_assembly_correct flattening_correct obtain \<Sigma>\<^sub>B' where SB': 
      "\<Sigma>\<^sub>B' \<in> StackToAssembly.state_convert (Flattening.state_convert \<Sigma>\<^sub>S') \<and> 
        iterate (eval_b_assembly ?\<Pi>\<^sub>B) \<Sigma>\<^sub>B \<Sigma>\<^sub>B'" by blast
    with ES DA B debranching_correct have SA': "iterate (eval_assembly ?\<Pi>\<^sub>A)
      (Debranching.state_convert (dom ?\<Pi>\<^sub>B) \<Sigma>\<^sub>B) (Debranching.state_convert (dom ?\<Pi>\<^sub>B) \<Sigma>\<^sub>B')" by blast
    with DF linearization_correct have SL': "iterate (eval_l_assembly (linearize ?\<Pi>\<^sub>A)) 
      (Linearization.state_convert (Debranching.state_convert (dom ?\<Pi>\<^sub>B) \<Sigma>\<^sub>B)) 
        (Linearization.state_convert (Debranching.state_convert (dom ?\<Pi>\<^sub>B) \<Sigma>\<^sub>B'))" by blast
    with SA' B DL assembly_to_machine_correct obtain \<Sigma>\<^sub>M' where SM': 
      "\<Sigma>\<^sub>M' \<in> AssemblyToMachine.state_convert (linearize ?\<Pi>\<^sub>A) 
        (Linearization.state_convert (Debranching.state_convert (dom ?\<Pi>\<^sub>B) \<Sigma>\<^sub>B')) \<and> 
          iterate (eval_machine ?\<Pi>\<^sub>M) \<Sigma>\<^sub>M \<Sigma>\<^sub>M'" by blast
    with SA' SB' have "\<Sigma>\<^sub>M' \<in> { \<Sigma>\<^sub>M' | \<Sigma>\<^sub>B' \<Sigma>\<^sub>M'. 
      \<Sigma>\<^sub>B' \<in> StackToAssembly.state_convert (Flattening.state_convert \<Sigma>\<^sub>S') \<and> 
        \<Sigma>\<^sub>M' \<in> AssemblyToMachine.state_convert (linearize ?\<Pi>\<^sub>A) 
          (Linearization.state_convert (Debranching.state_convert (dom ?\<Pi>\<^sub>B) \<Sigma>\<^sub>B')) }" 
      by blast
    with SM' have "\<Sigma>\<^sub>M' \<in> state_convert \<Pi> \<Sigma>\<^sub>S' \<and> iterate (eval_machine (program_convert \<Pi>)) \<Sigma>\<^sub>M \<Sigma>\<^sub>M'"
      by (simp add: state_convert_def program_convert_def)
    thus ?thesis by fastforce
  qed

end