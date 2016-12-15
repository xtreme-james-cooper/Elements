theory Assembler
imports AssemblyLanguage MachineLanguage Iterate
begin

primrec machine_length :: "assembly \<Rightarrow> nat" where
  "machine_length (AAssm x) = 1"
| "machine_length (CAssm dst cmp) = 1"
| "machine_length (JAssm jmp s) = 2"

primrec converted_length :: "assembly list \<Rightarrow> nat" where
  "converted_length [] = 0"
| "converted_length (a # \<pi>) = machine_length a + converted_length \<pi>"

fun build_symbol_table :: "program \<Rightarrow> symbol \<rightharpoonup> nat" where
  "build_symbol_table [] s = None"
| "build_symbol_table ((s', \<pi>) # \<Pi>) s = (
    if s' = s then Some 0 
    else map_option (op + (converted_length \<pi>)) (build_symbol_table \<Pi> s))"

definition get_block_addr :: "(symbol \<rightharpoonup> nat) \<Rightarrow> symbol \<Rightarrow> int" where
  "get_block_addr \<rho> s = int (the (\<rho> s))"

primrec instruction_conv :: "(symbol \<rightharpoonup> nat) \<Rightarrow> assembly \<Rightarrow> instruction list" where
  "instruction_conv \<rho> (AAssm x) = [AInstr x]"
| "instruction_conv \<rho> (CAssm dst cmp) = [CInstr dst cmp {}]"
| "instruction_conv \<rho> (JAssm jmp s) = [AInstr (get_block_addr \<rho> s), CInstr {} (Reg D) jmp]"

definition get_assembly :: "program \<Rightarrow> assembly list" where
  "get_assembly \<Pi> = concat (map snd \<Pi>)"

definition program_convert :: "program \<Rightarrow> instruction list" where
  "program_convert \<Pi> = concat (map (instruction_conv (build_symbol_table \<Pi>)) (get_assembly \<Pi>))"

definition get_pc :: "program \<Rightarrow> assembly list \<Rightarrow> nat set" where
  "get_pc \<Pi> \<pi> = 
    { the (build_symbol_table \<Pi> s) + converted_length \<pi>' | s \<pi>'. lookup \<Pi> s = Some (\<pi>' @ \<pi>) }"

fun state_convert :: "program \<Rightarrow> assembly_state \<Rightarrow> machine_state set" where
  "state_convert \<Pi> (\<sigma>, Some a, d, \<pi>) = {(\<sigma>, a, d, pc) | pc. pc \<in> get_pc \<Pi> \<pi>}"
| "state_convert \<Pi> (\<sigma>, None, d, \<pi>) = {(\<sigma>, a, d, pc) | a pc. pc \<in> get_pc \<Pi> \<pi>}"

(* conversion correctness *)

lemma [simp]: "lookup \<Pi> s = Some \<pi> \<Longrightarrow> \<exists>n. build_symbol_table \<Pi> s = Some n"
  by (induction \<Pi> s rule: lookup.induct) auto

lemma [simp]: "lookup \<Pi> s = Some \<pi> \<Longrightarrow> nat (get_block_addr (build_symbol_table \<Pi>) s) \<in> get_pc \<Pi> \<pi>" 
  by (induction \<Pi> s rule: lookup.induct) (auto simp add: get_block_addr_def get_pc_def)

lemma instr_conv_len [simp]: "length (instruction_conv \<rho> a) = machine_length a"
  by (induction a) simp_all

lemma convert_expands [simp]: "length \<pi> \<le> converted_length \<pi>"
  proof (induction \<pi>)
  case Nil
    thus ?case by simp
  case (Cons a \<pi>)
    thus ?case by (induction a) simp_all
  qed

lemma [simp]: "length (concat (map (instruction_conv \<rho>) \<pi>)) = converted_length \<pi>"
  by (induction \<pi>) simp_all

lemma [simp]: "converted_length (\<pi> @ \<pi>') = converted_length \<pi> + converted_length \<pi>'"
  by (induction \<pi>) simp_all

lemma pc_within: "pc \<in> get_pc \<Pi> (a # \<pi>) \<Longrightarrow> 
    i < length (instruction_conv (build_symbol_table \<Pi>) a) \<Longrightarrow> i + pc < length (program_convert \<Pi>)"
  proof -
    assume "pc \<in> get_pc \<Pi> (a # \<pi>)" 
    then obtain s \<pi>' where P: "pc = the (build_symbol_table \<Pi> s) + converted_length \<pi>'" 
      and L: "lookup \<Pi> s = Some (\<pi>' @ a # \<pi>)" by (auto simp add: get_pc_def)
    assume "i < length (instruction_conv (build_symbol_table \<Pi>) a)"
    hence "i < machine_length a" by simp
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

lemma [simp]: "pc \<in> get_pc \<Pi> (a # \<pi>) \<Longrightarrow> pc < length (program_convert \<Pi>)"
  using pc_within by (induction a) fastforce+

lemma [simp]: "pc \<in> get_pc \<Pi> (JAssm jmp s # \<pi>) \<Longrightarrow> Suc pc < length (program_convert \<Pi>)"
  using pc_within by fastforce

lemma [simp]: "i < machine_length a \<Longrightarrow> (instruction_conv \<rho> a @ \<pi>) ! i = instruction_conv \<rho> a ! i"
  by (induction a) (simp_all, induction i, simp_all)

lemma lookup_convert': "i < machine_length a \<Longrightarrow> 
  concat (map (instruction_conv \<rho>) (\<pi> @ a # \<pi>')) ! (converted_length \<pi> + i) = 
    instruction_conv \<rho> a ! i"
  proof (induction \<pi>)
  case Nil
    thus ?case by simp
  next case (Cons a' \<pi>)
    hence "(instruction_conv \<rho> a' @ concat (map (instruction_conv \<rho>) (\<pi> @ a # \<pi>'))) ! 
        (length (instruction_conv \<rho> a') + converted_length \<pi> + i) = instruction_conv \<rho> a ! i" 
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
    assume D: "domain_distinct \<Pi>"
       and L: "lookup \<Pi> s = Some \<pi>"
       and I: "i < converted_length \<pi>"
    have "\<forall>x. build_symbol_table \<Pi> x = map_option (op + 0) (build_symbol_table \<Pi> x)"
      proof
        fix x
        show "build_symbol_table \<Pi> x = map_option (op + 0) (build_symbol_table \<Pi> x)" 
          by (cases "build_symbol_table \<Pi> x") simp_all
      qed
    with D L I have "program_convert \<Pi> ! (the (build_symbol_table \<Pi> s) - 0 + i) = 
        concat (map (instruction_conv (build_symbol_table \<Pi>)) \<pi>) ! i" 
      by (metis lookup_convert'' program_convert_def)
    thus ?thesis by simp
  qed

lemma lookup_convert: "domain_distinct \<Pi> \<Longrightarrow> pc \<in> get_pc \<Pi> (a # \<pi>) \<Longrightarrow> i < machine_length a \<Longrightarrow>
    program_convert \<Pi> ! (pc + i) = instruction_conv (build_symbol_table \<Pi>) a ! i"
  proof -
    assume D: "domain_distinct \<Pi>"
    assume L: "i < machine_length a"
    assume "pc \<in> get_pc \<Pi> (a # \<pi>)" 
    then obtain s \<pi>' where P: "pc = the (build_symbol_table \<Pi> s) + converted_length \<pi>' \<and> 
      lookup \<Pi> s = Some (\<pi>' @ a # \<pi>)" by (auto simp add: get_pc_def)
    from D L lookup_convert' P show ?thesis by (simp add: add.assoc)
  qed

lemma [simp]: "pc \<in> get_pc \<Pi> (AAssm x # \<pi>) \<Longrightarrow> Suc pc \<in> get_pc \<Pi> \<pi>"
  proof -
    assume "pc \<in> get_pc \<Pi> (AAssm x # \<pi>)"
    then obtain s \<pi>' where P: "pc = the (build_symbol_table \<Pi> s) + converted_length \<pi>' \<and> 
      lookup \<Pi> s = Some (\<pi>' @ AAssm x # \<pi>)" by (auto simp add: get_pc_def)
    with P have "Suc pc = the (build_symbol_table \<Pi> s) + converted_length (\<pi>' @ [AAssm x])" by simp
    with P get_pc_def show ?thesis by fastforce
  qed

lemma [simp]: "pc \<in> get_pc \<Pi> (CAssm dst cmp # \<pi>) \<Longrightarrow> Suc pc \<in> get_pc \<Pi> \<pi>"
  proof -
    assume "pc \<in> get_pc \<Pi> (CAssm dst cmp # \<pi>)"
    then obtain s \<pi>' where P: "pc = the (build_symbol_table \<Pi> s) + converted_length \<pi>' \<and> 
      lookup \<Pi> s = Some (\<pi>' @ CAssm dst cmp # \<pi>)" by (auto simp add: get_pc_def)
    with P have "Suc pc = the (build_symbol_table \<Pi> s) + converted_length (\<pi>' @ [CAssm dst cmp])" 
      by simp
    with P get_pc_def show ?thesis by fastforce
  qed

lemma [simp]: "pc \<in> get_pc \<Pi> (JAssm jmp s # \<pi>) \<Longrightarrow> Suc (Suc pc) \<in> get_pc \<Pi> \<pi>"
  proof -
    assume "pc \<in> get_pc \<Pi> (JAssm jmp s # \<pi>)"
    then obtain s' \<pi>' where P: "pc = the (build_symbol_table \<Pi> s') + converted_length \<pi>' \<and> 
      lookup \<Pi> s' = Some (\<pi>' @ JAssm jmp s # \<pi>)" by (auto simp add: get_pc_def)
    with P have "Suc (Suc pc) = 
      the (build_symbol_table \<Pi> s') + converted_length (\<pi>' @ [JAssm jmp s])" by simp
    with P get_pc_def show ?thesis by fastforce
  qed

lemma [simp]: "\<Sigma> \<in> state_convert \<Pi> (\<sigma>, a, d, \<pi>) \<Longrightarrow> \<exists>aa pc. \<Sigma> = (\<sigma>, aa, d, pc) \<and> pc \<in> get_pc \<Pi> \<pi>"
  by (cases a) auto

lemma eval_assembly_conv [simp]: "domain_distinct \<Pi> \<Longrightarrow> eval_assembly \<Pi> \<Sigma> = Some \<Sigma>\<^sub>1 \<Longrightarrow> 
  \<Sigma>' \<in> state_convert \<Pi> \<Sigma> \<Longrightarrow>
    \<exists>\<Sigma>\<^sub>1'. \<Sigma>\<^sub>1' \<in> state_convert \<Pi> \<Sigma>\<^sub>1 \<and> iterate (eval_machine (program_convert \<Pi>)) \<Sigma>' \<Sigma>\<^sub>1'"
  proof (induction \<Pi> \<Sigma> rule: eval_assembly.induct)
  case 1
    thus ?case by simp
  next case (2 \<Pi> \<sigma> a d x \<pi>)
    from 2 have S: "\<Sigma>\<^sub>1 = (\<sigma>, Some x, d, \<pi>)" by simp
    from 2 obtain pc aa where P: "\<Sigma>' = (\<sigma>, aa, d, pc) \<and> pc \<in> get_pc \<Pi> (AAssm x # \<pi>)" by fastforce
    hence X: "(\<sigma>, x, d, Suc pc) \<in> state_convert \<Pi> (\<sigma>, Some x, d, \<pi>)" by auto
    from 2 P lookup_convert have "eval_machine (program_convert \<Pi>) (\<sigma>, aa, d, pc) = 
      Some (\<sigma>, x, d, Suc pc)" by fastforce
    with X S P show ?case by fast
  next case (3 \<Pi> \<sigma> a d dst cmp \<pi>)
    let ?n = "compute cmp (\<sigma> a) a d"
    let ?\<sigma> = "if M \<in> dst then \<sigma>(a := ?n) else \<sigma>"
    let ?a = "if A \<in> dst then ?n else a"
    let ?d = "if D \<in> dst then ?n else d"
    from 3 have S: "\<Sigma>\<^sub>1 = (?\<sigma>, Some ?a, ?d, \<pi>)" by (simp add: Let_def)
    from 3 obtain pc where P: "\<Sigma>' = (\<sigma>, a, d, pc) \<and> pc \<in> get_pc \<Pi> (CAssm dst cmp # \<pi>)" by fastforce
    hence X: "(?\<sigma>, ?a, ?d, Suc pc) \<in> state_convert \<Pi> (?\<sigma>, Some ?a, ?d, \<pi>)" by auto
    have "eval_instruction (CInstr dst cmp {}) (\<sigma>, a, d, pc) = (?\<sigma>, ?a, ?d, Suc pc)" 
      by (simp add: Let_def)
    with 3 P lookup_convert have "eval_machine (program_convert \<Pi>) (\<sigma>, a, d, pc) = 
      Some (?\<sigma>, ?a, ?d, Suc pc)" by fastforce
    with X S P show ?case by fast
  next case 4
    thus ?case by simp
  next case (5 \<Pi> \<sigma> a d jmp s \<pi>)
    then obtain pc aa where P: "\<Sigma>' = (\<sigma>, aa, d, pc) \<and> pc \<in> get_pc \<Pi> (JAssm jmp s # \<pi>)" by fastforce
    let ?s = "get_block_addr (build_symbol_table \<Pi>) s"
    from 5 P lookup_convert have first_step: "eval_machine (program_convert \<Pi>) (\<sigma>, aa, d, pc) = 
      Some (\<sigma>, ?s, d, Suc pc)" by fastforce
    show ?case
      proof (cases "should_jump d jmp")
      case True
        thus ?thesis
          proof (cases "lookup \<Pi> s")
          case (Some \<pi>')
            with 5 True have S: "\<Sigma>\<^sub>1 = (\<sigma>, None, d, \<pi>')" by simp
            from Some have X: "(\<sigma>, ?s, d, nat ?s) \<in> state_convert \<Pi> (\<sigma>, None, d, \<pi>')" by simp
            have "1 < machine_length (JAssm jmp s)" by simp
            with 5 P lookup_convert True have "eval_machine (program_convert \<Pi>) (\<sigma>, ?s, d, Suc pc) = 
              Some (\<sigma>, ?s, d, nat ?s)" by fastforce
            with first_step X P S show ?thesis by fast
          next case None
            with 5 True show ?thesis by simp
          qed
      next case False
        from 5 False have S: "\<Sigma>\<^sub>1 = (\<sigma>, None, d, \<pi>)" by auto
        from P have X: "(\<sigma>, ?s, d, Suc (Suc pc)) \<in> state_convert \<Pi> (\<sigma>, None, d, \<pi>)" by auto
        from False have Y: "eval_instruction (CInstr {} (Reg D) jmp) (\<sigma>, ?s, d, Suc pc) = 
          (\<sigma>, ?s, d, Suc (Suc pc))" by auto
        have "1 < machine_length (JAssm jmp s)" by simp
        with 5 P Y lookup_convert have "eval_machine (program_convert \<Pi>) (\<sigma>, ?s, d, Suc pc) =
          Some (\<sigma>, ?s, d, Suc (Suc pc))" by fastforce
        with first_step X P S show ?thesis by fast
      qed
  qed

theorem [simp]: "iterate (eval_assembly \<Pi>) \<Sigma> \<Sigma>\<^sub>1 \<Longrightarrow> \<Sigma>' \<in> state_convert \<Pi> \<Sigma> \<Longrightarrow> 
  domain_distinct \<Pi> \<Longrightarrow> 
    \<exists>\<Sigma>\<^sub>1'. \<Sigma>\<^sub>1' \<in> state_convert \<Pi> \<Sigma>\<^sub>1 \<and> iterate (eval_machine (program_convert \<Pi>)) \<Sigma>' \<Sigma>\<^sub>1'"
  proof (induction "eval_assembly \<Pi>" \<Sigma> \<Sigma>\<^sub>1 arbitrary: \<Sigma>' rule: iterate.induct)
  case iter_refl
    thus ?case by fastforce
  next case (iter_step \<Sigma> \<Sigma>\<^sub>1 \<Sigma>\<^sub>2)
    then obtain \<Sigma>\<^sub>1' where S: "\<Sigma>\<^sub>1' \<in> state_convert \<Pi> \<Sigma>\<^sub>1 \<and> 
      iterate (eval_machine (program_convert \<Pi>)) \<Sigma>' \<Sigma>\<^sub>1'" by blast
    with iter_step eval_assembly_conv obtain \<Sigma>\<^sub>2' where
      "\<Sigma>\<^sub>2' \<in> state_convert \<Pi> \<Sigma>\<^sub>2 \<and> iterate (eval_machine (program_convert \<Pi>)) \<Sigma>\<^sub>1' \<Sigma>\<^sub>2'" by blast
    with S have "\<Sigma>\<^sub>2' \<in> state_convert \<Pi> \<Sigma>\<^sub>2 \<and> iterate (eval_machine (program_convert \<Pi>)) \<Sigma>' \<Sigma>\<^sub>2'" 
      by fastforce
    thus ?case by blast
  qed

end