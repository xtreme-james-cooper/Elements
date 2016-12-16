theory TotalCorrectness
imports AssemblyToMachine StackToAssembly
begin

definition state_convert :: "stack_program \<Rightarrow> stack_state \<Rightarrow> machine_state set" where
  "state_convert \<Pi> \<Sigma> = {\<Sigma>'' | \<Sigma>' \<Sigma>''. 
    \<Sigma>' \<in> StackToAssembly.state_convert \<Sigma> \<and> 
      \<Sigma>'' \<in> AssemblyToMachine.state_convert (StackToAssembly.program_convert \<Pi>) \<Sigma>'}"

definition program_convert :: "stack_program \<Rightarrow> machine_program" where
  "program_convert \<Pi> = AssemblyToMachine.program_convert (StackToAssembly.program_convert \<Pi>)"

theorem total_correctness: "iterate (eval_stack \<Pi>) \<Sigma> \<Sigma>\<^sub>1 \<Longrightarrow> \<Sigma>' \<in> state_convert \<Pi> \<Sigma> \<Longrightarrow> 
    domain_distinct \<Pi> \<Longrightarrow> 
      \<exists>\<Sigma>\<^sub>1'. \<Sigma>\<^sub>1' \<in> state_convert \<Pi> \<Sigma>\<^sub>1 \<and> iterate (eval_machine (program_convert \<Pi>)) \<Sigma>' \<Sigma>\<^sub>1'"
  proof -
    assume "iterate (eval_stack \<Pi>) \<Sigma> \<Sigma>\<^sub>1"
    assume "\<Sigma>' \<in> state_convert \<Pi> \<Sigma>"
    assume "domain_distinct \<Pi>" 
    
have "iterate (eval_assembly p\<Pi>) p\<Sigma> p\<Sigma>\<^sub>1 \<Longrightarrow> p\<Sigma>' \<in> AssemblyToMachine.state_convert p\<Pi> p\<Sigma> \<Longrightarrow> 
  domain_distinct p\<Pi> \<Longrightarrow> 
    \<exists>\<Sigma>\<^sub>1'. \<Sigma>\<^sub>1' \<in> AssemblyToMachine.state_convert p\<Pi> p\<Sigma>\<^sub>1 \<and> iterate (eval_machine (AssemblyToMachine.program_convert p\<Pi>)) p\<Sigma>' \<Sigma>\<^sub>1'" by (metis assembly_to_machine_correct)

have "iterate (eval_stack pp\<Pi>) pp\<Sigma> pp\<Sigma>\<^sub>1 \<Longrightarrow> pp\<Sigma>' \<in> StackToAssembly.state_convert pp\<Sigma> \<Longrightarrow> 
    \<exists>\<Sigma>\<^sub>1'. \<Sigma>\<^sub>1' \<in> StackToAssembly.state_convert pp\<Sigma>\<^sub>1 \<and> iterate (eval_assembly (StackToAssembly.program_convert pp\<Pi>)) pp\<Sigma>' \<Sigma>\<^sub>1'" by (metis stack_to_assembly_correct)


    have "\<exists>\<Sigma>\<^sub>1'. \<Sigma>\<^sub>1' \<in> state_convert \<Pi> \<Sigma>\<^sub>1 \<and> iterate (eval_machine (program_convert \<Pi>)) \<Sigma>' \<Sigma>\<^sub>1'" by simp
    thus ?thesis by simp
  qed

end