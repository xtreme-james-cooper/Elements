theory TotalCorrectness
imports AssemblyToMachine Debranching StackToAssembly
begin

definition state_convert :: "stack_program \<Rightarrow> stack_state \<Rightarrow> machine_state set" where
  "state_convert \<Pi> \<Sigma>\<^sub>S = {\<Sigma>\<^sub>M | \<Sigma>\<^sub>B \<Sigma>\<^sub>M. 
    \<Sigma>\<^sub>B \<in> StackToAssembly.state_convert \<Sigma>\<^sub>S \<and> 
      \<Sigma>\<^sub>M \<in> AssemblyToMachine.state_convert 
        (linearize (debranch (StackToAssembly.program_convert \<Pi>))) 
          (Debranching.state_convert (dom (StackToAssembly.program_convert \<Pi>)) \<Sigma>\<^sub>B)}"

definition program_convert :: "stack_program \<Rightarrow> machine_program" where
  "program_convert \<Pi> =
    AssemblyToMachine.program_convert (linearize (debranch (StackToAssembly.program_convert \<Pi>)))"

theorem total_correctness: "finite (dom \<Pi>) \<Longrightarrow> iterate (eval_stack \<Pi>) \<Sigma>\<^sub>S \<Sigma>\<^sub>S' \<Longrightarrow> 
  \<Sigma>\<^sub>M \<in> state_convert \<Pi> \<Sigma>\<^sub>S \<Longrightarrow> 
    \<exists>\<Sigma>\<^sub>M'. \<Sigma>\<^sub>M' \<in> state_convert \<Pi> \<Sigma>\<^sub>S' \<and> iterate (eval_machine (program_convert \<Pi>)) \<Sigma>\<^sub>M \<Sigma>\<^sub>M'"
  proof -
    assume D: "finite (dom \<Pi>)"
    hence DL: "domain_distinct (linearize (debranch (StackToAssembly.program_convert \<Pi>)))" by simp
    from D have DF: "finite (dom (debranch (StackToAssembly.program_convert \<Pi>)))" by simp
    assume ES: "iterate (eval_stack \<Pi>) \<Sigma>\<^sub>S \<Sigma>\<^sub>S'"
    assume "\<Sigma>\<^sub>M \<in> state_convert \<Pi> \<Sigma>\<^sub>S"
    with state_convert_def obtain \<Sigma>\<^sub>B where SA: "\<Sigma>\<^sub>B \<in> StackToAssembly.state_convert \<Sigma>\<^sub>S \<and> 
        \<Sigma>\<^sub>M \<in> AssemblyToMachine.state_convert 
          (linearize (debranch (StackToAssembly.program_convert \<Pi>))) 
            (Debranching.state_convert (dom (StackToAssembly.program_convert \<Pi>)) \<Sigma>\<^sub>B)" 
      by blast
    with ES stack_to_assembly_correct obtain \<Sigma>\<^sub>B' where SA': 
      "\<Sigma>\<^sub>B' \<in> StackToAssembly.state_convert \<Sigma>\<^sub>S' \<and> 
        iterate (eval_b_assembly (StackToAssembly.program_convert \<Pi>)) \<Sigma>\<^sub>B \<Sigma>\<^sub>B'" by blast
    let ?\<Sigma>\<^sub>A = "Debranching.state_convert (dom (StackToAssembly.program_convert \<Pi>)) \<Sigma>\<^sub>B"
    let ?\<Sigma>\<^sub>A' = "Debranching.state_convert (dom (StackToAssembly.program_convert \<Pi>)) \<Sigma>\<^sub>B'"
    from SA' ES debranching_correct have 
      "iterate (eval_assembly (debranch (StackToAssembly.program_convert \<Pi>))) ?\<Sigma>\<^sub>A ?\<Sigma>\<^sub>A'" by blast
    with DF linearization_correct have 
      "iterate (eval_l_assembly (linearize (debranch (StackToAssembly.program_convert \<Pi>)))) 
        ?\<Sigma>\<^sub>A ?\<Sigma>\<^sub>A'" by blast
    with SA DL assembly_to_machine_correct obtain \<Sigma>\<^sub>M' where SM': 
      "\<Sigma>\<^sub>M' \<in> AssemblyToMachine.state_convert 
        (linearize (debranch (StackToAssembly.program_convert \<Pi>))) ?\<Sigma>\<^sub>A' \<and> 
          iterate (eval_machine (AssemblyToMachine.program_convert 
            (linearize (debranch (StackToAssembly.program_convert \<Pi>))))) \<Sigma>\<^sub>M \<Sigma>\<^sub>M'" by blast
    with SA' have "\<Sigma>\<^sub>M' \<in> {\<Sigma>\<^sub>M' | \<Sigma>\<^sub>B' \<Sigma>\<^sub>M'. 
      \<Sigma>\<^sub>B' \<in> StackToAssembly.state_convert \<Sigma>\<^sub>S' \<and> 
        \<Sigma>\<^sub>M' \<in> AssemblyToMachine.state_convert 
          (linearize (debranch (StackToAssembly.program_convert \<Pi>)))  
            (Debranching.state_convert (dom (StackToAssembly.program_convert \<Pi>)) \<Sigma>\<^sub>B')}" by blast
    with SM' have "\<Sigma>\<^sub>M' \<in> state_convert \<Pi> \<Sigma>\<^sub>S' \<and> iterate (eval_machine (program_convert \<Pi>)) \<Sigma>\<^sub>M \<Sigma>\<^sub>M'"
      by (simp add: state_convert_def program_convert_def)
    thus ?thesis by fastforce
  qed

end