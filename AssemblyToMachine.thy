theory AssemblyToMachine
imports LinearAssemblyLanguage MachineLanguage Iterate
begin

primrec machine_length :: "assembly \<Rightarrow> nat" where
  "machine_length (AAssm x) = 1"
| "machine_length (CAssm dst cmp) = 1"
| "machine_length (JAssm jmp s) = 2"
| "machine_length PAssm = 1"

primrec converted_length :: "assembly list \<Rightarrow> nat" where
  "converted_length [] = 0"
| "converted_length (\<iota> # \<pi>) = machine_length \<iota> + converted_length \<pi>"

fun build_symbol_table :: "l_assembly_program \<Rightarrow> code_label \<rightharpoonup> nat" where
  "build_symbol_table [] s = None"
| "build_symbol_table ((s', \<pi>) # \<Pi>) s = (
    if s' = s then Some 0 
    else map_option (op + (converted_length \<pi>)) (build_symbol_table \<Pi> s))"

definition get_block_addr :: "(code_label \<rightharpoonup> nat) \<Rightarrow> code_label \<Rightarrow> int" where
  "get_block_addr \<rho> s = int (the (\<rho> s))"

primrec instruction_conv :: "(code_label \<rightharpoonup> nat) \<Rightarrow> assembly \<Rightarrow> machine_program" where
  "instruction_conv \<rho> (AAssm x) = [AInstr x]"
| "instruction_conv \<rho> (CAssm dst cmp) = [CInstr dst cmp {}]"
| "instruction_conv \<rho> (JAssm jmp s) = [AInstr (get_block_addr \<rho> s), CInstr {} (Reg D) jmp]"
| "instruction_conv \<rho> PAssm = [PInstr]"

definition get_assembly :: "l_assembly_program \<Rightarrow> assembly list" where
  "get_assembly \<Pi> = concat (map snd \<Pi>)"

definition program_convert :: "l_assembly_program \<Rightarrow> machine_program" where
  "program_convert \<Pi> = concat (map (instruction_conv (build_symbol_table \<Pi>)) (get_assembly \<Pi>))"

definition get_pc :: "l_assembly_program \<Rightarrow> assembly list \<Rightarrow> nat set" where
  "get_pc \<Pi> \<pi> = 
    { the (build_symbol_table \<Pi> s) + converted_length \<pi>' | s \<pi>'. lookup \<Pi> s = Some (\<pi>' @ \<pi>) }"

fun state_convert :: "l_assembly_program \<Rightarrow> assembly_state \<Rightarrow> machine_state set" where
  "state_convert \<Pi> (\<mu>, Some a, d, \<pi>, \<omega>) = {(\<mu>, a, d, pc, \<omega>) | pc. pc \<in> get_pc \<Pi> \<pi>}"
| "state_convert \<Pi> (\<mu>, None, d, \<pi>, \<omega>) = {(\<mu>, a, d, pc, \<omega>) | a pc. pc \<in> get_pc \<Pi> \<pi>}"

(* conversion correctness *)

lemma [simp]: "lookup \<Pi> s = Some \<pi> \<Longrightarrow> \<exists>n. build_symbol_table \<Pi> s = Some n"
  by (induction \<Pi> s rule: lookup.induct) auto

lemma [simp]: "lookup \<Pi> s = Some \<pi> \<Longrightarrow> nat (get_block_addr (build_symbol_table \<Pi>) s) \<in> get_pc \<Pi> \<pi>" 
  by (induction \<Pi> s rule: lookup.induct) (auto simp add: get_block_addr_def get_pc_def)

lemma instr_conv_len [simp]: "length (instruction_conv \<rho> \<iota>) = machine_length \<iota>"
  by (induction \<iota>) simp_all

lemma convert_expands [simp]: "length \<pi> \<le> converted_length \<pi>"
  proof (induction \<pi>)
  case Nil
    thus ?case by simp
  case (Cons \<iota> \<pi>)
    thus ?case by (induction \<iota>) simp_all
  qed

lemma [simp]: "length (concat (map (instruction_conv \<rho>) \<pi>)) = converted_length \<pi>"
  by (induction \<pi>) simp_all

lemma [simp]: "converted_length (\<pi> @ \<pi>') = converted_length \<pi> + converted_length \<pi>'"
  by (induction \<pi>) simp_all

lemma pc_within: "pc \<in> get_pc \<Pi> (\<iota> # \<pi>) \<Longrightarrow> 
    i < length (instruction_conv (build_symbol_table \<Pi>) \<iota>) \<Longrightarrow> i + pc < length (program_convert \<Pi>)"
  proof -
    assume "pc \<in> get_pc \<Pi> (\<iota> # \<pi>)" 
    then obtain s \<pi>' where P: "pc = the (build_symbol_table \<Pi> s) + converted_length \<pi>'" 
      and L: "lookup \<Pi> s = Some (\<pi>' @ \<iota> # \<pi>)" by (auto simp add: get_pc_def)
    assume "i < length (instruction_conv (build_symbol_table \<Pi>) \<iota>)"
    hence "i < machine_length \<iota>" by simp
    with L have "i + the (build_symbol_table \<Pi> s) + converted_length \<pi>' < 
        length (program_convert \<Pi>)"
      proof (induction \<Pi> s rule: build_symbol_table.induct)
      case 1
        thus ?case by simp
      next case (2 s' \<pi>'' \<Pi> s)
        thus ?case
          proof (cases "s' = s")
          case True
            with 2 show ?thesis by (simp add: program_convert_def get_assembly_def)
          next case False
            with 2 show ?thesis
              by (cases "build_symbol_table \<Pi> s") 
                 (simp_all add: program_convert_def get_assembly_def)
          qed
      qed
    with P show ?thesis by simp
  qed

lemma [simp]: "pc \<in> get_pc \<Pi> (\<iota> # \<pi>) \<Longrightarrow> pc < length (program_convert \<Pi>)"
  using pc_within by (induction \<iota>) fastforce+

lemma [simp]: "pc \<in> get_pc \<Pi> (JAssm jmp s # \<pi>) \<Longrightarrow> Suc pc < length (program_convert \<Pi>)"
  using pc_within by fastforce

lemma [simp]: "i < machine_length \<iota> \<Longrightarrow> (instruction_conv \<rho> \<iota> @ \<pi>) ! i = instruction_conv \<rho> \<iota> ! i"
  by (induction \<iota>) (simp_all, induction i, simp_all)

lemma lookup_convert': "i < machine_length \<iota> \<Longrightarrow> 
  concat (map (instruction_conv \<rho>) (\<pi> @ \<iota> # \<pi>')) ! (converted_length \<pi> + i) = 
    instruction_conv \<rho> \<iota> ! i"
  proof (induction \<pi>)
  case Nil
    thus ?case by simp
  next case (Cons \<iota>' \<pi>)
    hence "(instruction_conv \<rho> \<iota>' @ concat (map (instruction_conv \<rho>) (\<pi> @ \<iota> # \<pi>'))) ! 
        (length (instruction_conv \<rho> \<iota>') + converted_length \<pi> + i) = instruction_conv \<rho> \<iota> ! i" 
      by (simp add: add.assoc del: instr_conv_len)
    thus ?case by simp
  qed

lemma symtab_conversion: "domain_distinct ((s', \<pi>) # \<Pi>) \<Longrightarrow> \<forall>s \<in> insert s' (dom (lookup \<Pi>)). 
  \<rho> s = map_option (op + n) (build_symbol_table ((s', \<pi>) # \<Pi>) s) \<Longrightarrow> 
    \<forall>s \<in> dom (lookup \<Pi>). \<rho> s = map_option (op + (n + converted_length \<pi>)) (build_symbol_table \<Pi> s)"
  proof 
    fix s
    assume "domain_distinct ((s', \<pi>) # \<Pi>)"
    moreover assume "s \<in> dom (lookup \<Pi>)"
    moreover then obtain m where "build_symbol_table \<Pi> s = Some m" by fastforce
    moreover assume "\<forall>x \<in> insert s' (dom (lookup \<Pi>)). 
      \<rho> x = map_option (op + n) (build_symbol_table ((s', \<pi>) # \<Pi>) x)"
    ultimately show "\<rho> s = map_option (op + (n + converted_length \<pi>)) (build_symbol_table \<Pi> s)"
      by auto
  qed

lemma lookup_convert'': "domain_distinct \<Pi> \<Longrightarrow> lookup \<Pi> s = Some \<pi> \<Longrightarrow> i < converted_length \<pi> \<Longrightarrow> 
  \<forall>x \<in> dom (lookup \<Pi>). \<rho> x = map_option (op + n) (build_symbol_table \<Pi> x) \<Longrightarrow>
    concat (map (instruction_conv \<rho>) (get_assembly \<Pi>)) ! (the (\<rho> s) - n + i) = 
      concat (map (instruction_conv \<rho>) \<pi>) ! i"
  proof (induction \<Pi> s arbitrary: n rule: lookup.induct)
  case 1
    thus ?case by simp
  next case (2 s' \<pi>' \<Pi> s)
    thus ?case
      proof (cases "s' = s")
      case True
        with 2 have "\<rho> s = Some n" by force                      
        with 2 True show ?thesis by (simp add: get_assembly_def nth_append)
      next case False
        let ?xs = "concat (map (instruction_conv \<rho>) \<pi>')"
        let ?ys = "concat (map (instruction_conv \<rho>) (get_assembly \<Pi>))"
        let ?n = "the (\<rho> s) - n + i"
        from False 2 obtain m where M: "build_symbol_table \<Pi> s = Some m" by fastforce
        from 2 have "\<forall>x\<in>dom (lookup ((s', \<pi>') # \<Pi>)). 
          \<rho> x = map_option (op + n) (build_symbol_table ((s', \<pi>') # \<Pi>) x)" by blast
        hence "\<forall>x\<in>insert s' (dom (lookup \<Pi>)). 
          \<rho> x = map_option (op + n) (build_symbol_table ((s', \<pi>') # \<Pi>) x)" by fastforce
        with 2 symtab_conversion have H: "\<forall>x \<in> dom (lookup \<Pi>). 
          \<rho> x = map_option (op + (n + converted_length \<pi>')) (build_symbol_table \<Pi> x)" by blast
        with 2 False M have "\<rho> s = Some (n + converted_length \<pi>' + m)" by force
        hence "(if ?n < converted_length \<pi>' then ?xs ! ?n else ?ys ! (?n - converted_length \<pi>')) = 
          ?ys ! (the (\<rho> s) - n - converted_length \<pi>' + i)" by simp
        with 2 False H show ?thesis by (auto simp add: get_assembly_def nth_append)
      qed
  qed

lemma [simp]: "domain_distinct \<Pi> \<Longrightarrow> lookup \<Pi> s = Some \<pi> \<Longrightarrow> i < converted_length \<pi> \<Longrightarrow> 
  program_convert \<Pi> ! (the (build_symbol_table \<Pi> s) + i) = 
    concat (map (instruction_conv (build_symbol_table \<Pi>)) \<pi>) ! i"
  proof -
    assume "domain_distinct \<Pi>"
       and "lookup \<Pi> s = Some \<pi>"
       and "i < converted_length \<pi>"
    moreover have "\<forall>x. build_symbol_table \<Pi> x = map_option (op + 0) (build_symbol_table \<Pi> x)"
      proof
        fix x
        show "build_symbol_table \<Pi> x = map_option (op + 0) (build_symbol_table \<Pi> x)" 
          by (cases "build_symbol_table \<Pi> x") simp_all
      qed
    ultimately have "program_convert \<Pi> ! (the (build_symbol_table \<Pi> s) - 0 + i) = 
        concat (map (instruction_conv (build_symbol_table \<Pi>)) \<pi>) ! i" 
      by (metis lookup_convert'' program_convert_def)
    thus ?thesis by simp
  qed

lemma lookup_convert: "domain_distinct \<Pi> \<Longrightarrow> pc \<in> get_pc \<Pi> (\<iota> # \<pi>) \<Longrightarrow> i < machine_length \<iota> \<Longrightarrow>
    program_convert \<Pi> ! (pc + i) = instruction_conv (build_symbol_table \<Pi>) \<iota> ! i"
  proof -
    assume D: "domain_distinct \<Pi>"
    assume L: "i < machine_length \<iota>"
    assume "pc \<in> get_pc \<Pi> (\<iota> # \<pi>)" 
    then obtain s \<pi>' where P: "pc = the (build_symbol_table \<Pi> s) + converted_length \<pi>' \<and> 
      lookup \<Pi> s = Some (\<pi>' @ \<iota> # \<pi>)" by (auto simp add: get_pc_def)
    from D L lookup_convert' P show ?thesis by (simp add: add.assoc)
  qed

lemma next_pc: "pc \<in> get_pc \<Pi> (\<iota> # \<pi>) \<Longrightarrow> machine_length \<iota> + pc \<in> get_pc \<Pi> \<pi>"
  proof (induction \<iota>)
  case (AAssm x)
    then obtain s \<pi>' where P: "pc = the (build_symbol_table \<Pi> s) + converted_length \<pi>' \<and> 
      lookup \<Pi> s = Some (\<pi>' @ AAssm x # \<pi>)" by (auto simp add: get_pc_def)
    with P have "Suc pc = the (build_symbol_table \<Pi> s) + converted_length (\<pi>' @ [AAssm x])" by simp
    with P get_pc_def show ?case by fastforce
  next case (CAssm dst cmp)
    then obtain s \<pi>' where P: "pc = the (build_symbol_table \<Pi> s) + converted_length \<pi>' \<and> 
      lookup \<Pi> s = Some (\<pi>' @ CAssm dst cmp # \<pi>)" by (auto simp add: get_pc_def)
    with P have "Suc pc = the (build_symbol_table \<Pi> s) + converted_length (\<pi>' @ [CAssm dst cmp])" 
      by simp
    with P get_pc_def show ?case by fastforce
  next case (JAssm jmp s)
    then obtain s' \<pi>' where P: "pc = the (build_symbol_table \<Pi> s') + converted_length \<pi>' \<and> 
      lookup \<Pi> s' = Some (\<pi>' @ JAssm jmp s # \<pi>)" by (auto simp add: get_pc_def)
    with P have "Suc (Suc pc) = 
      the (build_symbol_table \<Pi> s') + converted_length (\<pi>' @ [JAssm jmp s])" by simp
    with P get_pc_def show ?case by fastforce
  next case PAssm
    then obtain s \<pi>' where P: "pc = the (build_symbol_table \<Pi> s) + converted_length \<pi>' \<and> 
      lookup \<Pi> s = Some (\<pi>' @ PAssm # \<pi>)" by (auto simp add: get_pc_def)
    with P have "Suc pc = the (build_symbol_table \<Pi> s) + converted_length (\<pi>' @ [PAssm])" by simp
    with P get_pc_def show ?case by fastforce
  qed

lemma [simp]: "\<Sigma> \<in> state_convert \<Pi> (\<mu>, a, d, \<pi>, \<omega>) \<Longrightarrow> 
    \<exists>aa pc. \<Sigma> = (\<mu>, aa, d, pc, \<omega>) \<and> pc \<in> get_pc \<Pi> \<pi>"
  by (cases a) auto

lemma eval_assembly_conv [simp]: "domain_distinct \<Pi> \<Longrightarrow> eval_l_assembly \<Pi> \<Sigma>\<^sub>A = Some \<Sigma>\<^sub>A' \<Longrightarrow> 
  \<Sigma>\<^sub>M \<in> state_convert \<Pi> \<Sigma>\<^sub>A \<Longrightarrow>
    \<exists>\<Sigma>\<^sub>M'. \<Sigma>\<^sub>M' \<in> state_convert \<Pi> \<Sigma>\<^sub>A' \<and> iterate (eval_machine (program_convert \<Pi>)) \<Sigma>\<^sub>M \<Sigma>\<^sub>M'"
  proof (induction \<Pi> \<Sigma>\<^sub>A rule: eval_l_assembly.induct)
  case 1
    thus ?case by simp
  next case (2 \<Pi> \<mu> a d x \<pi> \<omega>)
    from 2 have S: "\<Sigma>\<^sub>A' = (\<mu>, Some x, d, \<pi>, \<omega>)" by simp
    from 2 obtain pc aa where P: "\<Sigma>\<^sub>M = (\<mu>, aa, d, pc, \<omega>) \<and> pc \<in> get_pc \<Pi> (AAssm x # \<pi>)" 
      by fastforce
    with next_pc have X: "(\<mu>, x, d, Suc pc, \<omega>) \<in> state_convert \<Pi> (\<mu>, Some x, d, \<pi>, \<omega>)" by fastforce
    from 2 P lookup_convert have "eval_machine (program_convert \<Pi>) (\<mu>, aa, d, pc, \<omega>) = 
      Some (\<mu>, x, d, Suc pc, \<omega>)" by fastforce
    with X S P iter_one show ?case by fast
  next case (3 \<Pi> \<mu> a d dst cmp \<pi> \<omega>)
    let ?n = "compute cmp (\<mu> a) a d"
    let ?\<mu> = "if M \<in> dst then \<mu>(a := ?n) else \<mu>"
    let ?a = "if A \<in> dst then ?n else a"
    let ?d = "if D \<in> dst then ?n else d"
    from 3 have S: "\<Sigma>\<^sub>A' = (?\<mu>, Some ?a, ?d, \<pi>, \<omega>)" by (simp add: Let_def)
    from 3 obtain pc where P: "\<Sigma>\<^sub>M = (\<mu>, a, d, pc, \<omega>) \<and> pc \<in> get_pc \<Pi> (CAssm dst cmp # \<pi>)" 
      by fastforce
    with next_pc have X: "(?\<mu>, ?a, ?d, Suc pc, \<omega>) \<in> state_convert \<Pi> (?\<mu>, Some ?a, ?d, \<pi>, \<omega>)" 
      by fastforce
    have "eval_instruction (CInstr dst cmp {}) (\<mu>, a, d, pc, \<omega>) = (?\<mu>, ?a, ?d, Suc pc, \<omega>)" 
      by (simp add: Let_def)
    with 3 P lookup_convert have "eval_machine (program_convert \<Pi>) (\<mu>, a, d, pc, \<omega>) = 
      Some (?\<mu>, ?a, ?d, Suc pc, \<omega>)" by fastforce
    with X S P iter_one show ?case by fast
  next case 4
    thus ?case by simp
  next case (5 \<Pi> \<mu> a d jmp s \<pi> \<omega>)
    then obtain pc aa where P: "\<Sigma>\<^sub>M = (\<mu>, aa, d, pc, \<omega>) \<and> pc \<in> get_pc \<Pi> (JAssm jmp s # \<pi>)" 
      by fastforce
    let ?s = "get_block_addr (build_symbol_table \<Pi>) s"
    from 5 P lookup_convert have first_step: "eval_machine (program_convert \<Pi>) (\<mu>, aa, d, pc, \<omega>) = 
      Some (\<mu>, ?s, d, Suc pc, \<omega>)" by fastforce
    show ?case
      proof (cases "should_jump d jmp")
      case True
        thus ?thesis
          proof (cases "lookup \<Pi> s")
          case (Some \<pi>')
            with 5 True have S: "\<Sigma>\<^sub>A' = (\<mu>, None, d, \<pi>', \<omega>)" by simp
            from Some have X: "(\<mu>, ?s, d, nat ?s, \<omega>) \<in> state_convert \<Pi> (\<mu>, None, d, \<pi>', \<omega>)" by simp
            have "1 < machine_length (JAssm jmp s)" by simp
            with 5 P lookup_convert True have 
              "eval_machine (program_convert \<Pi>) (\<mu>, ?s, d, Suc pc, \<omega>) = 
                Some (\<mu>, ?s, d, nat ?s, \<omega>)" by fastforce
            with first_step X P S iter_two show ?thesis by fast
          next case None
            with 5 True show ?thesis by simp
          qed
      next case False
        from 5 False have S: "\<Sigma>\<^sub>A' = (\<mu>, None, d, \<pi>, \<omega>)" by auto
        from P next_pc have X: "(\<mu>, ?s, d, Suc (Suc pc), \<omega>) \<in> state_convert \<Pi> (\<mu>, None, d, \<pi>, \<omega>)" 
          by fastforce
        from False have Y: "eval_instruction (CInstr {} (Reg D) jmp) (\<mu>, ?s, d, Suc pc, \<omega>) = 
          (\<mu>, ?s, d, Suc (Suc pc), \<omega>)" by auto
        have "1 < machine_length (JAssm jmp s)" by simp
        with 5 P Y lookup_convert have "eval_machine (program_convert \<Pi>) (\<mu>, ?s, d, Suc pc, \<omega>) =
          Some (\<mu>, ?s, d, Suc (Suc pc), \<omega>)" by fastforce
        with first_step X P S iter_two show ?thesis by fast
      qed
  next case (6 \<Pi> \<mu> a d \<pi> \<omega>)
    thus ?case
      proof (cases a)
      case (Some aa)
        from 6 Some have S: "\<Sigma>\<^sub>A' = (\<mu>, Some aa, d, \<pi>, d # \<omega>)" by simp
        from 6 Some obtain pc where P: "\<Sigma>\<^sub>M = (\<mu>, aa, d, pc, \<omega>) \<and> pc \<in> get_pc \<Pi> (PAssm # \<pi>)" 
          by fastforce
        with next_pc have X: "(\<mu>, aa, d, Suc pc, d # \<omega>) \<in> state_convert \<Pi> (\<mu>, Some aa, d, \<pi>, d # \<omega>)" 
          by fastforce
        from 6 P lookup_convert have "eval_machine (program_convert \<Pi>) (\<mu>, aa, d, pc, \<omega>) = 
          Some (\<mu>, aa, d, Suc pc, d # \<omega>)" by fastforce
        with X S P iter_one show ?thesis by fast
      next case None
        from 6 None have S: "\<Sigma>\<^sub>A' = (\<mu>, None, d, \<pi>, d # \<omega>)" by simp
        from 6 obtain pc aa where P: "\<Sigma>\<^sub>M = (\<mu>, aa, d, pc, \<omega>) \<and> pc \<in> get_pc \<Pi> (PAssm # \<pi>)" 
          by fastforce
        with next_pc have X: "(\<mu>, aa, d, Suc pc, d # \<omega>) \<in> state_convert \<Pi> (\<mu>, None, d, \<pi>, d # \<omega>)" 
          by fastforce
        from 6 P lookup_convert have "eval_machine (program_convert \<Pi>) (\<mu>, aa, d, pc, \<omega>) = 
          Some (\<mu>, aa, d, Suc pc, d # \<omega>)" by fastforce
        with X S P iter_one show ?thesis by fast
      qed
  qed

theorem assembly_to_machine_correct [simp]: "iterate (eval_l_assembly \<Pi>) \<Sigma>\<^sub>A \<Sigma>\<^sub>A' \<Longrightarrow> 
  \<Sigma>\<^sub>M \<in> state_convert \<Pi> \<Sigma>\<^sub>A \<Longrightarrow> domain_distinct \<Pi> \<Longrightarrow> 
    \<exists>\<Sigma>\<^sub>M'. \<Sigma>\<^sub>M' \<in> state_convert \<Pi> \<Sigma>\<^sub>A' \<and> iterate (eval_machine (program_convert \<Pi>)) \<Sigma>\<^sub>M \<Sigma>\<^sub>M'"
  proof (induction "eval_l_assembly \<Pi>" \<Sigma>\<^sub>A \<Sigma>\<^sub>A' arbitrary: \<Sigma>\<^sub>M rule: iterate.induct)
  case iter_refl
    thus ?case by fastforce
  next case (iter_step \<Sigma>\<^sub>A \<Sigma>\<^sub>A' \<Sigma>\<^sub>A'')
    then obtain \<Sigma>\<^sub>M' where S: "\<Sigma>\<^sub>M' \<in> state_convert \<Pi> \<Sigma>\<^sub>A' \<and> 
      iterate (eval_machine (program_convert \<Pi>)) \<Sigma>\<^sub>M \<Sigma>\<^sub>M'" by blast
    with iter_step eval_assembly_conv obtain \<Sigma>\<^sub>M'' where
      "\<Sigma>\<^sub>M'' \<in> state_convert \<Pi> \<Sigma>\<^sub>A'' \<and> iterate (eval_machine (program_convert \<Pi>)) \<Sigma>\<^sub>M' \<Sigma>\<^sub>M''" by blast
    with S have "\<Sigma>\<^sub>M'' \<in> state_convert \<Pi> \<Sigma>\<^sub>A'' \<and> iterate (eval_machine (program_convert \<Pi>)) \<Sigma>\<^sub>M \<Sigma>\<^sub>M''" 
      by fastforce
    thus ?case by blast
  qed

end