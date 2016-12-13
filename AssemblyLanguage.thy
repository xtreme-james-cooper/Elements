theory AssemblyLanguage
imports MachineLanguage FiniteMap Iterate
begin

typedecl symbol

datatype assembly =
  AAssm int
| SAssm symbol
| CAssm "register set" computation "comparison set"

type_synonym program = "symbol \<leadsto> assembly list"

type_synonym assembly_state = "memory \<times> int \<times> int \<times> symbol \<times> assembly list" (* M, A, D, S, PC *)

fun eval_assembly :: "program \<Rightarrow> assembly_state \<Rightarrow> assembly_state option" where
  "eval_assembly \<Pi> (\<sigma>, a, d, s, []) = None"
| "eval_assembly \<Pi> (\<sigma>, a, d, s, AAssm x # \<pi>) = Some (\<sigma>, x, d, s, \<pi>)"
| "eval_assembly \<Pi> (\<sigma>, a, d, s, SAssm x # \<pi>) = Some (\<sigma>, a, d, x, \<pi>)"
| "eval_assembly \<Pi> (\<sigma>, a, d, s, CAssm dst cmp jmp # \<pi>) = (
    let n = compute cmp (\<sigma> (nat a)) a d
    in let \<sigma>' = if M \<in> dst then \<sigma>(nat a := n) else \<sigma>
    in let a' = if A \<in> dst then n else a
    in let d' = if D \<in> dst then n else d
    in if should_jump n jmp
       then case lookup \<Pi> s of 
           Some \<pi>' \<Rightarrow> Some (\<sigma>', a', d', s, \<pi>')
         | None \<Rightarrow> None
       else Some (\<sigma>', a', d', s, \<pi>))"

(* conversion *)

fun build_symbol_table :: "program \<Rightarrow> symbol \<rightharpoonup> nat" where
  "build_symbol_table [] s = None"
| "build_symbol_table ((s', \<pi>) # \<Pi>) s = (
    if s' = s then Some 0 
    else map_option (op + (length \<pi>)) (build_symbol_table \<Pi> s))"

primrec instruction_conv :: "(symbol \<rightharpoonup> nat) \<Rightarrow> assembly \<Rightarrow> instruction" where
  "instruction_conv \<rho> (AAssm x) = AInstr x"
| "instruction_conv \<rho> (SAssm x) = AInstr (int (the (\<rho> x)))"
| "instruction_conv \<rho> (CAssm dst cmp jmp) = CInstr dst cmp jmp"

definition get_assembly :: "program \<Rightarrow> assembly list" where
  "get_assembly \<Pi> = concat (map snd \<Pi>)"

definition program_convert :: "program \<Rightarrow> instruction list" where
  "program_convert \<Pi> = map (instruction_conv (build_symbol_table \<Pi>)) (get_assembly \<Pi>)"

definition get_pc :: "program \<Rightarrow> assembly list \<Rightarrow> nat set" where
  "get_pc \<Pi> \<pi> = { the (build_symbol_table \<Pi> s) + length \<pi>'' | s \<pi>' \<pi>''. 
    s \<in> dom (lookup \<Pi>) \<and> lookup \<Pi> s = Some \<pi>' \<and> \<pi>' = \<pi>'' @ \<pi> }"

definition get_block_addr :: "program \<Rightarrow> symbol \<Rightarrow> int" where
  "get_block_addr \<Pi> s = int (the (build_symbol_table \<Pi> s))"

fun state_convert :: "program \<Rightarrow> assembly_state \<Rightarrow> machine_state set" where
  "state_convert \<Pi> (\<sigma>, a, d, s, \<pi>) = 
    (\<lambda>pc. (\<sigma>, a, d, pc)) ` get_pc \<Pi> \<pi> \<union> (\<lambda>pc. (\<sigma>, get_block_addr \<Pi> s, d, pc)) ` get_pc \<Pi> \<pi>"

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

lemma [simp]: "pc \<in> get_pc \<Pi> (a # \<pi>) \<Longrightarrow> 
    program_convert \<Pi> ! pc = instruction_conv (build_symbol_table \<Pi>) a"
  by (auto simp add: get_pc_def program_convert_def)

lemma eval_assembly_conv [simp]: "eval_assembly \<Pi> \<sigma> = Some \<sigma>\<^sub>1 \<Longrightarrow> \<sigma>' \<in> state_convert \<Pi> \<sigma> \<Longrightarrow>
    \<exists>\<sigma>\<^sub>1'. \<sigma>\<^sub>1' \<in> state_convert \<Pi> \<sigma>\<^sub>1 \<and> eval (program_convert \<Pi>) \<sigma>' = Some \<sigma>\<^sub>1'"
  proof (induction \<Pi> \<sigma> rule: eval_assembly.induct)
  case (1 \<Pi> \<sigma> a d s)
    thus ?case by simp
  next case (2 \<Pi> \<sigma> a d s x \<pi>)
    from 2 have "\<sigma>' \<in> (\<lambda>pc. (\<sigma>, a, d, pc)) ` get_pc \<Pi> (AAssm x # \<pi>) \<union> (\<lambda>pc. (\<sigma>, get_block_addr \<Pi> s, d, pc)) ` get_pc \<Pi> (AAssm x # \<pi>)" by simp



    have "\<sigma>\<^sub>1' \<in> (\<lambda>pc. (\<sigma>, x, d, pc)) ` get_pc \<Pi> \<pi> \<and> eval (program_convert \<Pi>) \<sigma>' = Some \<sigma>\<^sub>1'" by simp
    with 2 show ?case by fastforce
  next case (3 \<Pi> \<sigma> a d s x \<pi>)
    thus ?case by simp
  next case (4 \<Pi> \<sigma> a d s dst cmp jmp \<pi>)
    thus ?case by simp
  qed

theorem [simp]: "iterate (eval_assembly \<Pi>) \<sigma> \<sigma>\<^sub>1 \<Longrightarrow> \<sigma>' \<in> state_convert \<Pi> \<sigma> \<Longrightarrow>
    \<exists>\<sigma>\<^sub>1'. \<sigma>\<^sub>1' \<in> state_convert \<Pi> \<sigma>\<^sub>1 \<and> iterate (eval (program_convert \<Pi>)) \<sigma>' \<sigma>\<^sub>1'"
  proof (induction "eval_assembly \<Pi>" \<sigma> \<sigma>\<^sub>1 arbitrary: \<sigma>' rule: iterate.induct)
  case iter_refl
    thus ?case by fastforce
  next case (iter_step \<sigma> \<sigma>\<^sub>1 \<sigma>\<^sub>2)
    then obtain \<sigma>\<^sub>1' where S: "\<sigma>\<^sub>1' \<in> state_convert \<Pi> \<sigma>\<^sub>1 \<and> iterate (eval (program_convert \<Pi>)) \<sigma>' \<sigma>\<^sub>1'" 
      by blast
    with iter_step eval_assembly_conv obtain \<sigma>\<^sub>2' where
      "\<sigma>\<^sub>2' \<in> state_convert \<Pi> \<sigma>\<^sub>2 \<and> eval (program_convert \<Pi>) \<sigma>\<^sub>1' = Some \<sigma>\<^sub>2'" by blast
    with S have "\<sigma>\<^sub>2' \<in> state_convert \<Pi> \<sigma>\<^sub>2 \<and> iterate (eval (program_convert \<Pi>)) \<sigma>' \<sigma>\<^sub>2'" by fastforce
    thus ?case by blast
  qed

end