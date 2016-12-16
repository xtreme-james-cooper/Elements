theory TotalCorrectness
imports AssemblyToMachine StackToAssembly
begin

definition state_convert :: "stack_program \<Rightarrow> stack_state \<Rightarrow> machine_state set" where
  "state_convert \<Pi> \<Sigma>\<^sub>S = {\<Sigma>\<^sub>M | \<Sigma>\<^sub>A \<Sigma>\<^sub>M. 
    \<Sigma>\<^sub>A \<in> StackToAssembly.state_convert \<Sigma>\<^sub>S \<and> 
      \<Sigma>\<^sub>M \<in> AssemblyToMachine.state_convert (StackToAssembly.program_convert \<Pi>) \<Sigma>\<^sub>A}"

definition program_convert :: "stack_program \<Rightarrow> machine_program" where
  "program_convert \<Pi> = AssemblyToMachine.program_convert (StackToAssembly.program_convert \<Pi>)"

theorem total_correctness: "iterate (eval_stack \<Pi>) \<Sigma>\<^sub>S \<Sigma>\<^sub>S' \<Longrightarrow> \<Sigma>\<^sub>M \<in> state_convert \<Pi> \<Sigma>\<^sub>S \<Longrightarrow> 
    domain_distinct \<Pi> \<Longrightarrow> 
      \<exists>\<Sigma>\<^sub>M'. \<Sigma>\<^sub>M' \<in> state_convert \<Pi> \<Sigma>\<^sub>S' \<and> iterate (eval_machine (program_convert \<Pi>)) \<Sigma>\<^sub>M \<Sigma>\<^sub>M'"
  proof -
    assume ES: "iterate (eval_stack \<Pi>) \<Sigma>\<^sub>S \<Sigma>\<^sub>S'"
    assume "domain_distinct \<Pi>" 
    hence D: "domain_distinct (StackToAssembly.program_convert \<Pi>)" by simp
    assume "\<Sigma>\<^sub>M \<in> state_convert \<Pi> \<Sigma>\<^sub>S"
    with state_convert_def obtain \<Sigma>\<^sub>A where SA: "\<Sigma>\<^sub>A \<in> StackToAssembly.state_convert \<Sigma>\<^sub>S \<and> 
      \<Sigma>\<^sub>M \<in> AssemblyToMachine.state_convert (StackToAssembly.program_convert \<Pi>) \<Sigma>\<^sub>A" by blast
    with ES stack_to_assembly_correct obtain \<Sigma>\<^sub>A' where SA': 
      "\<Sigma>\<^sub>A' \<in> StackToAssembly.state_convert \<Sigma>\<^sub>S' \<and> 
        iterate (eval_assembly (StackToAssembly.program_convert \<Pi>)) \<Sigma>\<^sub>A \<Sigma>\<^sub>A'" by blast
    with SA D assembly_to_machine_correct obtain \<Sigma>\<^sub>M' where SM': 
      "\<Sigma>\<^sub>M' \<in> AssemblyToMachine.state_convert (StackToAssembly.program_convert \<Pi>) \<Sigma>\<^sub>A' \<and> 
        iterate (eval_machine 
          (AssemblyToMachine.program_convert (StackToAssembly.program_convert \<Pi>))) \<Sigma>\<^sub>M \<Sigma>\<^sub>M'" by blast
    with SA' have "\<Sigma>\<^sub>M' \<in> {\<Sigma>\<^sub>M' | \<Sigma>\<^sub>A' \<Sigma>\<^sub>M'. 
      \<Sigma>\<^sub>A' \<in> StackToAssembly.state_convert \<Sigma>\<^sub>S' \<and> 
        \<Sigma>\<^sub>M' \<in> AssemblyToMachine.state_convert (StackToAssembly.program_convert \<Pi>) \<Sigma>\<^sub>A'}" by blast
    with SM' have "\<Sigma>\<^sub>M' \<in> state_convert \<Pi> \<Sigma>\<^sub>S' \<and> iterate (eval_machine (program_convert \<Pi>)) \<Sigma>\<^sub>M \<Sigma>\<^sub>M'" 
      by (simp add: state_convert_def program_convert_def)
    thus ?thesis by fastforce
  qed

end