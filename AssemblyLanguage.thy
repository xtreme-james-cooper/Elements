theory AssemblyLanguage
imports MachineLanguage FiniteMap Iterate
begin

typedecl symbol

datatype assembly =
  AAssm int
| CAssm "register set" computation
| JAssm "comparison set" symbol

type_synonym program = "symbol \<leadsto> assembly list"

type_synonym assembly_state = "memory \<times> int \<times> int \<times> assembly list" (* M, A, D, PC *)

fun eval_assembly :: "program \<Rightarrow> assembly_state \<Rightarrow> assembly_state option" where
  "eval_assembly \<Pi> (\<sigma>, a, d, []) = None"
| "eval_assembly \<Pi> (\<sigma>, a, d, AAssm x # \<pi>) = Some (\<sigma>, x, d, \<pi>)"
| "eval_assembly \<Pi> (\<sigma>, a, d, CAssm dst cmp # \<pi>) = (
    let n = compute cmp (\<sigma> (nat a)) a d
    in Some (
      if M \<in> dst then \<sigma>(nat a := n) else \<sigma>, 
      if A \<in> dst then n else a, 
      if D \<in> dst then n else d, 
      \<pi>))"
| "eval_assembly \<Pi> (\<sigma>, a, d, JAssm jmp s # \<pi>) = (
    if should_jump d jmp
    then case lookup \<Pi> s of 
        Some \<pi>' \<Rightarrow> Some (\<sigma>, a, d, \<pi>')
      | None \<Rightarrow> None
    else Some (\<sigma>, a, d, \<pi>))"

(* conversion *)

fun build_symbol_table :: "program \<Rightarrow> symbol \<rightharpoonup> nat" where
  "build_symbol_table [] s = None"
| "build_symbol_table ((s', \<pi>) # \<Pi>) s = (
    if s' = s then Some 0 
    else map_option (op + (length \<pi>)) (build_symbol_table \<Pi> s))"

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
  "state_convert \<Pi> (\<sigma>, a, d, \<pi>) = (\<lambda>pc. (\<sigma>, a, d, pc)) ` get_pc \<Pi> \<pi>"

(* conversion correctness *)

lemma [simp]: "lookup \<Pi> s = Some \<pi> \<Longrightarrow> \<exists>n. build_symbol_table \<Pi> s = Some n"
  by (induction \<Pi> s rule: lookup.induct) auto

lemma [simp]: "lookup \<Pi> s = Some \<pi> \<Longrightarrow> n < length \<pi> \<Longrightarrow> 
    the (build_symbol_table \<Pi> s) + n < length (get_assembly \<Pi>)"
  proof (induction \<Pi> s rule: build_symbol_table.induct)
  case 1
    thus ?case by simp
  next case (2 s' \<pi>' \<Pi> s)
    thus ?case
      proof (cases "s' = s")
      case True
        with 2 show ?thesis by (simp add: get_assembly_def)
      next case False
        with 2 obtain m where "build_symbol_table \<Pi> s = Some m" by fastforce
        with 2 False show ?thesis by (simp add: get_assembly_def)
      qed
  qed

lemma [simp]: "1 \<le> length (instruction_conv \<rho> a)"
  by (induction a) simp_all

lemma [simp]: "length \<pi> \<le> length (concat (map (instruction_conv \<rho>) \<pi>))"
  apply (induction \<pi>) apply simp_all by simp

lemma [simp]: "lookup \<Pi> s = Some (\<pi> @ \<pi>') \<Longrightarrow> \<pi>' \<noteq> [] \<Longrightarrow>
    the (build_symbol_table \<Pi> s) + length \<pi> < length (program_convert \<Pi>)"
  proof (induction \<Pi> s rule: build_symbol_table.induct)
  case 1
    thus ?case by simp
  next case (2 s' \<pi>' \<Pi> s)
    thus ?case
      proof (cases "s' = s")
      case True
        with 2 show ?thesis apply (simp add: program_convert_def get_assembly_def) by simp
      next case False
        with 2 obtain m where "build_symbol_table \<Pi> s = Some m" by fastforce
        with 2 False show ?thesis by (simp add: program_convert_def get_assembly_def)
      qed
  qed

lemma [simp]: "lookup \<Pi> s = Some \<pi> \<Longrightarrow> n < length \<pi> \<Longrightarrow>  
    get_assembly \<Pi> ! (the (build_symbol_table \<Pi> s) + n) = \<pi> ! n"
  proof (induction \<Pi> s rule: build_symbol_table.induct)
  case 1
    thus ?case by simp
  next case (2 s' \<pi>' \<Pi> s)
    thus ?case
      proof (cases "s' = s")
      case True
        with 2 show ?thesis by (simp add: get_assembly_def nth_append)
      next case False
        with 2 obtain m where "build_symbol_table \<Pi> s = Some m" by fastforce
        with 2 False show ?thesis by (simp add: get_assembly_def add.assoc)      
      qed
  qed

lemma [simp]: "pc \<in> get_pc \<Pi> (a # \<pi>) \<Longrightarrow> i < length (instruction_conv (build_symbol_table \<Pi>) a) \<Longrightarrow>
    program_convert \<Pi> ! (pc + i) = instruction_conv (build_symbol_table \<Pi>) a ! i"
  by (auto simp add: get_pc_def program_convert_def)

lemma [simp]: "pc \<in> get_pc \<Pi> (a # \<pi>) \<Longrightarrow> pc < length (program_convert \<Pi>)"
  by (auto simp add: get_pc_def)

lemma [simp]: "pc \<in> get_pc \<Pi> (a # \<pi>) \<Longrightarrow> Suc pc \<in> get_pc \<Pi> \<pi>"
  proof -
    assume "pc \<in> get_pc \<Pi> (a # \<pi>)"
    then obtain s \<pi>' where P: "pc = the (build_symbol_table \<Pi> s) + length \<pi>' \<and> 
      lookup \<Pi> s = Some (\<pi>' @ a # \<pi>)" by (auto simp add: get_pc_def)
    hence "the (build_symbol_table \<Pi> s) + length (\<pi>' @ [a]) \<in> 
      { the (build_symbol_table \<Pi> s) + length \<pi>' | s \<pi>'. lookup \<Pi> s = Some (\<pi>' @ \<pi>) }" by fastforce
    with P show "Suc pc \<in> get_pc \<Pi> \<pi>" by (simp add: get_pc_def)
  qed

lemma eval_assembly_conv [simp]: "eval_assembly \<Pi> \<Sigma> = Some \<Sigma>\<^sub>1 \<Longrightarrow> \<Sigma>' \<in> state_convert \<Pi> \<Sigma> \<Longrightarrow>
    \<exists>\<Sigma>\<^sub>1'. \<Sigma>\<^sub>1' \<in> state_convert \<Pi> \<Sigma>\<^sub>1 \<and> eval (program_convert \<Pi>) \<Sigma>' = Some \<Sigma>\<^sub>1'"
  proof (induction \<Pi> \<Sigma> rule: eval_assembly.induct)
  case 1
    thus ?case by simp
  next case 2
    thus ?case by simp
  next case 3
    thus ?case by simp
  next case 4
    thus ?case by simp
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
      "\<Sigma>\<^sub>2' \<in> state_convert \<Pi> \<Sigma>\<^sub>2 \<and> eval (program_convert \<Pi>) \<Sigma>\<^sub>1' = Some \<Sigma>\<^sub>2'" by blast
    with S have "\<Sigma>\<^sub>2' \<in> state_convert \<Pi> \<Sigma>\<^sub>2 \<and> iterate (eval (program_convert \<Pi>)) \<Sigma>' \<Sigma>\<^sub>2'" 
      by fastforce
    thus ?case by blast
  qed

end