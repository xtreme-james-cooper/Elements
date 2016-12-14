theory AssemblyLanguage
imports MachineLanguage FiniteMap Iterate
begin

typedecl symbol

datatype assembly =
  AAssm int
| CAssm "register set" computation
| JAssm "comparison set" symbol

type_synonym program = "symbol \<leadsto> assembly list"

type_synonym assembly_state = "memory \<times> int option \<times> int \<times> assembly list" (* M, A, D, PC *)

fun eval_assembly :: "program \<Rightarrow> assembly_state \<Rightarrow> assembly_state option" where
  "eval_assembly \<Pi> (\<sigma>, a, d, []) = None"
| "eval_assembly \<Pi> (\<sigma>, a, d, AAssm x # \<pi>) = Some (\<sigma>, Some x, d, \<pi>)"
| "eval_assembly \<Pi> (\<sigma>, Some a, d, CAssm dst cmp # \<pi>) = (
    let n = compute cmp (\<sigma> a) a d
    in Some (
      if M \<in> dst then \<sigma>(a := n) else \<sigma>, 
      Some (if A \<in> dst then n else a), 
      if D \<in> dst then n else d, 
      \<pi>))"
| "eval_assembly \<Pi> (\<sigma>, None, d, CAssm dst cmp # \<pi>) = None"
| "eval_assembly \<Pi> (\<sigma>, a, d, JAssm jmp s # \<pi>) = (
    if should_jump d jmp
    then case lookup \<Pi> s of 
        Some \<pi>' \<Rightarrow> Some (\<sigma>, None, d, \<pi>')
      | None \<Rightarrow> None
    else Some (\<sigma>, None, d, \<pi>))"

(* conversion *)

fun get_converted_length :: "assembly list \<Rightarrow> nat" where
  "get_converted_length [] = 0"
| "get_converted_length (AAssm x # \<pi>) = Suc (get_converted_length \<pi>)"
| "get_converted_length (CAssm dst cmp # \<pi>) = Suc (get_converted_length \<pi>)"
| "get_converted_length (JAssm jmp s # \<pi>) = Suc (Suc (get_converted_length \<pi>))"

fun build_symbol_table :: "program \<Rightarrow> symbol \<rightharpoonup> nat" where
  "build_symbol_table [] s = None"
| "build_symbol_table ((s', \<pi>) # \<Pi>) s = (
    if s' = s then Some 0 
    else map_option (op + (get_converted_length \<pi>)) (build_symbol_table \<Pi> s))"

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
  "get_pc \<Pi> \<pi> = { the (build_symbol_table \<Pi> s) + length \<pi>' | s \<pi>'. lookup \<Pi> s = Some (\<pi>' @ \<pi>) }"

fun state_convert :: "program \<Rightarrow> assembly_state \<Rightarrow> machine_state set" where
  "state_convert \<Pi> (\<sigma>, Some a, d, \<pi>) = {(\<sigma>, a, d, pc) | pc. pc \<in> get_pc \<Pi> \<pi>}"
| "state_convert \<Pi> (\<sigma>, None, d, \<pi>) = {(\<sigma>, a, d, pc) | a pc. pc \<in> get_pc \<Pi> \<pi>}"

(* conversion correctness *)

lemma [simp]: "lookup \<Pi> s = Some \<pi> \<Longrightarrow> \<exists>n. build_symbol_table \<Pi> s = Some n"
  by (induction \<Pi> s rule: lookup.induct) auto

lemma [simp]: "lookup \<Pi> s = Some \<pi> \<Longrightarrow> nat (get_block_addr (build_symbol_table \<Pi>) s) \<in> get_pc \<Pi> \<pi>" 
  proof (induction \<Pi> s rule: lookup.induct)
  case 1
    thus ?case by simp
  next case 2
    thus ?case by simp
  qed

lemma convert_expands [simp]: "length \<pi> \<le> get_converted_length \<pi>"
  by (induction \<pi> rule: get_converted_length.induct) simp_all

lemma [simp]: "length (concat (map (instruction_conv \<rho>) \<pi>)) = get_converted_length \<pi>"
  by (induction \<pi> rule: get_converted_length.induct) simp_all

lemma [simp]: "lookup \<Pi> s = Some (\<pi> @ \<pi>') \<Longrightarrow> \<pi>' \<noteq> [] \<Longrightarrow>
    the (build_symbol_table \<Pi> s) + length \<pi> < length (program_convert \<Pi>)"
  proof (induction \<Pi> s rule: build_symbol_table.induct)
  case 1
    thus ?case by simp
  next case (2 s' \<pi>'' \<Pi> s)
    let ?\<rho> = "build_symbol_table ((s', \<pi>'') # \<Pi>)"
    show ?case
      proof (cases "s' = s")
      case True
        from 2 have "0 < length \<pi>'" by simp 
        hence X: "0 < get_converted_length \<pi>'" by (metis convert_expands gr0I leD)
        have "length \<pi> \<le> get_converted_length \<pi>" by simp
        with X have "length \<pi> < get_converted_length \<pi> + get_converted_length \<pi>'" by linarith
        with 2 True show ?thesis by (simp add: program_convert_def get_assembly_def)
      next case False
        with 2 obtain n where "build_symbol_table \<Pi> s = Some n" by fastforce
        with 2 False show ?thesis 
          by (simp add: program_convert_def get_assembly_def add.assoc add_le_less_mono)
      qed
  qed

lemma [simp]: "pc \<in> get_pc \<Pi> (a # \<pi>) \<Longrightarrow> pc < length (program_convert \<Pi>)"
  by (auto simp add: get_pc_def)

lemma [simp]: "pc \<in> get_pc \<Pi> (JAssm jmp s # \<pi>) \<Longrightarrow> Suc pc < length (program_convert \<Pi>)"
  by (auto simp add: get_pc_def)

lemma lookup_convert: "pc \<in> get_pc \<Pi> (a # \<pi>) \<Longrightarrow> 
  i < length (instruction_conv (build_symbol_table \<Pi>) a) \<Longrightarrow>
    program_convert \<Pi> ! (pc + i) = instruction_conv (build_symbol_table \<Pi>) a ! i"
  proof -
    assume "i < length (instruction_conv (build_symbol_table \<Pi>) a)"
    assume "pc \<in> get_pc \<Pi> (a # \<pi>)" 
    then obtain s \<pi>' where P :"pc = the (build_symbol_table \<Pi> s) + length \<pi>' \<and> 
      lookup \<Pi> s = Some (\<pi>' @ a # \<pi>)" by (auto simp add: get_pc_def)


    have "concat (map (instruction_conv (build_symbol_table \<Pi>)) (get_assembly \<Pi>)) ! (the (build_symbol_table \<Pi> s) + length \<pi>' + i) = 
      instruction_conv (build_symbol_table \<Pi>) a ! i" by simp
    with P show ?thesis by (simp add: program_convert_def)
  qed

lemma [simp]: "pc \<in> get_pc \<Pi> (a # \<pi>) \<Longrightarrow> Suc pc \<in> get_pc \<Pi> \<pi>"
  proof -
    assume "pc \<in> get_pc \<Pi> (a # \<pi>)"
    then obtain s \<pi>' where P: "pc = the (build_symbol_table \<Pi> s) + length \<pi>' \<and> 
      lookup \<Pi> s = Some (\<pi>' @ a # \<pi>)" by (auto simp add: get_pc_def)
    hence "the (build_symbol_table \<Pi> s) + length (\<pi>' @ [a]) \<in> 
      { the (build_symbol_table \<Pi> s) + length \<pi>' | s \<pi>'. lookup \<Pi> s = Some (\<pi>' @ \<pi>) }" by fastforce
    with P show ?thesis by (simp add: get_pc_def)
  qed

lemma [simp]: "pc \<in> get_pc \<Pi> (JAssm jmp s # \<pi>) \<Longrightarrow> Suc (Suc pc) \<in> get_pc \<Pi> \<pi>"
  proof -
    assume "pc \<in> get_pc \<Pi> (JAssm jmp s # \<pi>)"
    have "Suc (Suc pc) \<in> get_pc \<Pi> \<pi>" by simp
    thus ?thesis by simp
  qed

lemma [simp]: "\<Sigma> \<in> state_convert \<Pi> (\<sigma>, a, d, \<pi>) \<Longrightarrow> \<exists>aa pc. \<Sigma> = (\<sigma>, aa, d, pc) \<and> pc \<in> get_pc \<Pi> \<pi>"
  by (cases a) auto

lemma eval_assembly_conv [simp]: "eval_assembly \<Pi> \<Sigma> = Some \<Sigma>\<^sub>1 \<Longrightarrow> \<Sigma>' \<in> state_convert \<Pi> \<Sigma> \<Longrightarrow>
    \<exists>\<Sigma>\<^sub>1'. \<Sigma>\<^sub>1' \<in> state_convert \<Pi> \<Sigma>\<^sub>1 \<and> iterate (eval (program_convert \<Pi>)) \<Sigma>' \<Sigma>\<^sub>1'"
  proof (induction \<Pi> \<Sigma> rule: eval_assembly.induct)
  case 1
    thus ?case by simp
  next case (2 \<Pi> \<sigma> a d x \<pi>)
    from 2 have S: "\<Sigma>\<^sub>1 = (\<sigma>, Some x, d, \<pi>)" by simp
    from 2 obtain pc aa where P: "\<Sigma>' = (\<sigma>, aa, d, pc) \<and> pc \<in> get_pc \<Pi> (AAssm x # \<pi>)" by fastforce
    hence X: "(\<sigma>, x, d, Suc pc) \<in> state_convert \<Pi> (\<sigma>, Some x, d, \<pi>)" by auto
    from P lookup_convert have "eval (program_convert \<Pi>) (\<sigma>, aa, d, pc) = Some (\<sigma>, x, d, Suc pc)" 
      by fastforce
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
    with P lookup_convert have "eval (program_convert \<Pi>) (\<sigma>, a, d, pc) = Some (?\<sigma>, ?a, ?d, Suc pc)" 
      by fastforce
    with X S P show ?case by fast
  next case 4
    thus ?case by simp
  next case (5 \<Pi> \<sigma> a d jmp s \<pi>)
    then obtain pc aa where P: "\<Sigma>' = (\<sigma>, aa, d, pc) \<and> pc \<in> get_pc \<Pi> (JAssm jmp s # \<pi>)" by fastforce
    let ?s = "get_block_addr (build_symbol_table \<Pi>) s"
    from P lookup_convert have first_step: "eval (program_convert \<Pi>) (\<sigma>, aa, d, pc) = 
      Some (\<sigma>, ?s, d, Suc pc)" by fastforce
    show ?case
      proof (cases "should_jump d jmp")
      case True
        thus ?thesis
          proof (cases "lookup \<Pi> s")
          case (Some \<pi>')
            with 5 True have S: "\<Sigma>\<^sub>1 = (\<sigma>, None, d, \<pi>')" by simp
            from Some have X: "(\<sigma>, ?s, d, nat ?s) \<in> state_convert \<Pi> (\<sigma>, None, d, \<pi>')" by simp
            from P lookup_convert True have "eval (program_convert \<Pi>) (\<sigma>, ?s, d, Suc pc) = 
              Some (\<sigma>, ?s, d, nat ?s)" by fastforce
            with first_step X P S show ?thesis by fast
          next case None
            with 5 True show ?thesis by simp
          qed
      next case False
        from 5 False have S: "\<Sigma>\<^sub>1 = (\<sigma>, None, d, \<pi>)" by auto
        from P have X: "(\<sigma>, ?s, d, Suc (Suc pc)) \<in> state_convert \<Pi> (\<sigma>, None, d, \<pi>)" by auto
        from False have "eval_instruction (CInstr {} (Reg D) jmp) (\<sigma>, ?s, d, Suc pc) = 
          (\<sigma>, ?s, d, Suc (Suc pc))" by auto
        with P lookup_convert have "eval (program_convert \<Pi>) (\<sigma>, ?s, d, Suc pc) =
          Some (\<sigma>, ?s, d, Suc (Suc pc))" by fastforce
        with first_step X P S show ?thesis by fast
      qed
  qed

theorem [simp]: "iterate (eval_assembly \<Pi>) \<Sigma> \<Sigma>\<^sub>1 \<Longrightarrow> \<Sigma>' \<in> state_convert \<Pi> \<Sigma> \<Longrightarrow> 
    \<exists>\<Sigma>\<^sub>1'. \<Sigma>\<^sub>1' \<in> state_convert \<Pi> \<Sigma>\<^sub>1 \<and> iterate (eval (program_convert \<Pi>)) \<Sigma>' \<Sigma>\<^sub>1'"
  proof (induction "eval_assembly \<Pi>" \<Sigma> \<Sigma>\<^sub>1 arbitrary: \<Sigma>' rule: iterate.induct)
  case iter_refl
    thus ?case by fastforce
  next case (iter_step \<Sigma> \<Sigma>\<^sub>1 \<Sigma>\<^sub>2)
    then obtain \<Sigma>\<^sub>1' where S: "\<Sigma>\<^sub>1' \<in> state_convert \<Pi> \<Sigma>\<^sub>1 \<and> 
      iterate (eval (program_convert \<Pi>)) \<Sigma>' \<Sigma>\<^sub>1'" by blast
    with iter_step eval_assembly_conv obtain \<Sigma>\<^sub>2' where
      "\<Sigma>\<^sub>2' \<in> state_convert \<Pi> \<Sigma>\<^sub>2 \<and> iterate (eval (program_convert \<Pi>)) \<Sigma>\<^sub>1' \<Sigma>\<^sub>2'" by blast
    with S have "\<Sigma>\<^sub>2' \<in> state_convert \<Pi> \<Sigma>\<^sub>2 \<and> iterate (eval (program_convert \<Pi>)) \<Sigma>' \<Sigma>\<^sub>2'" 
      by fastforce
    thus ?case by blast
  qed

end