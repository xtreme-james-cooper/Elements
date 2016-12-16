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
    assume "iterate (eval_stack \<Pi>) \<Sigma>\<^sub>S \<Sigma>\<^sub>S'"
    assume "domain_distinct \<Pi>" 
    assume "\<Sigma>\<^sub>M \<in> state_convert \<Pi> \<Sigma>\<^sub>S"

have "iterate (eval_assembly (StackToAssembly.program_convert \<Pi>)) p\<Sigma> p\<Sigma>\<^sub>1 \<Longrightarrow> p\<Sigma>' \<in> AssemblyToMachine.state_convert (StackToAssembly.program_convert \<Pi>) p\<Sigma> \<Longrightarrow> 
  domain_distinct (StackToAssembly.program_convert \<Pi>) \<Longrightarrow> 
    \<exists>\<Sigma>\<^sub>1'. \<Sigma>\<^sub>1' \<in> AssemblyToMachine.state_convert (StackToAssembly.program_convert \<Pi>) p\<Sigma>\<^sub>1 \<and> iterate (eval_machine (AssemblyToMachine.program_convert (StackToAssembly.program_convert \<Pi>))) p\<Sigma>' \<Sigma>\<^sub>1'" by (metis assembly_to_machine_correct)

have "iterate (eval_stack \<Pi>) \<Sigma> \<Sigma>\<^sub>1 \<Longrightarrow> pp\<Sigma>' \<in> StackToAssembly.state_convert \<Sigma> \<Longrightarrow> 
    \<exists>\<Sigma>\<^sub>1'. \<Sigma>\<^sub>1' \<in> StackToAssembly.state_convert \<Sigma>\<^sub>1 \<and> iterate (eval_assembly (StackToAssembly.program_convert \<Pi>)) pp\<Sigma>' \<Sigma>\<^sub>1'" by (metis stack_to_assembly_correct)


    have "\<Sigma>\<^sub>M' \<in> {\<Sigma>\<^sub>M' | \<Sigma>\<^sub>A' \<Sigma>\<^sub>M'. 
    \<Sigma>\<^sub>A' \<in> StackToAssembly.state_convert \<Sigma>\<^sub>S' \<and> 
      \<Sigma>\<^sub>M' \<in> AssemblyToMachine.state_convert (StackToAssembly.program_convert \<Pi>) \<Sigma>\<^sub>A'} \<and> 
      iterate (eval_machine (AssemblyToMachine.program_convert (StackToAssembly.program_convert \<Pi>))) \<Sigma>\<^sub>M \<Sigma>\<^sub>M'" by simp
    hence "\<Sigma>\<^sub>M' \<in> state_convert \<Pi> \<Sigma>\<^sub>S' \<and> iterate (eval_machine (program_convert \<Pi>)) \<Sigma>\<^sub>M \<Sigma>\<^sub>M'" by (simp add: state_convert_def program_convert_def)
    thus ?thesis by fastforce
  qed

end