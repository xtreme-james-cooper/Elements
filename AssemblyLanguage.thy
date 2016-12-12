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

fun block_size :: "assembly list \<Rightarrow> nat" where
  "block_size [] = 0"
| "block_size (AAssm x # as) = Suc (block_size as)"
| "block_size (SAssm x # as) = block_size as"
| "block_size (CAssm dst cmp jmp # as) = Suc (block_size as)"

fun build_symbol_table :: "program \<Rightarrow> symbol \<rightharpoonup> nat" where
  "build_symbol_table [] s = None"
| "build_symbol_table ((s', \<pi>) # \<Pi>) s = (
    if s' = s 
    then Some 0 
    else map_option (op + (block_size \<pi>)) (build_symbol_table \<Pi> s))"

primrec instruction_conv :: "(symbol \<rightharpoonup> nat) \<Rightarrow> assembly \<Rightarrow> instruction" where
  "instruction_conv \<rho> (AAssm x) = AInstr x"
| "instruction_conv \<rho> (SAssm x) = AInstr (int (the (\<rho> x)))"
| "instruction_conv \<rho> (CAssm dst cmp jmp) = CInstr dst cmp jmp"

fun program_convert' :: "(symbol \<rightharpoonup> nat) \<Rightarrow> program \<Rightarrow> instruction list" where
  "program_convert' \<rho> [] = []"
| "program_convert' \<rho> ((s, \<pi>) # \<Pi>) = map (instruction_conv \<rho>) \<pi> @ program_convert' \<rho> \<Pi>"

definition program_convert :: "program \<Rightarrow> instruction list" where
  "program_convert \<Pi> = program_convert' (build_symbol_table \<Pi>) \<Pi>"

fun state_convert :: "program \<Rightarrow> assembly_state \<Rightarrow> machine_state" where
  "state_convert \<Pi> (\<sigma>, a, d, s, \<pi>) = (\<sigma>, a, d, undefined)"

(* conversion correctness *)

lemma [simp]: "eval_assembly \<Pi> \<sigma> = Some \<sigma>\<^sub>1 \<Longrightarrow> 
    iterate (eval (program_convert \<Pi>)) (state_convert \<Pi> \<sigma>) (state_convert \<Pi> \<sigma>\<^sub>1)"
  proof (induction \<Pi> \<sigma> rule: eval_assembly.induct)
  case (1 \<Pi> \<sigma> a d s)
    thus ?case by simp
  next case (2 \<Pi> \<sigma> a d s x \<pi>)
    hence "eval_assembly \<Pi> (\<sigma>, a, d, s, AAssm x # \<pi>) = Some \<sigma>\<^sub>1" by simp



    have "iterate (eval (program_convert \<Pi>)) (state_convert \<Pi> (\<sigma>, a, d, s, AAssm x # \<pi>)) (state_convert \<Pi> \<sigma>\<^sub>1)" by simp
    thus ?case by simp
  next case (3 \<Pi> \<sigma> a d s x \<pi>)
    hence "eval_assembly \<Pi> (\<sigma>, a, d, s, SAssm x # \<pi>) = Some \<sigma>\<^sub>1" by simp



    have "iterate (eval (program_convert \<Pi>)) (state_convert \<Pi> (\<sigma>, a, d, s, SAssm x # \<pi>)) (state_convert \<Pi> \<sigma>\<^sub>1)" by simp
    thus ?case by simp
  next case (4 \<Pi> \<sigma> a d s dst cmp jmp \<pi>)
    hence "eval_assembly \<Pi> (\<sigma>, a, d, s, CAssm dst cmp jmp # \<pi>) = Some \<sigma>\<^sub>1" by simp



    have "iterate (eval (program_convert \<Pi>)) (state_convert \<Pi> (\<sigma>, a, d, s, CAssm dst cmp jmp # \<pi>)) (state_convert \<Pi> \<sigma>\<^sub>1)" by simp
    thus ?case by simp
  qed

theorem [simp]: "iterate (eval_assembly \<Pi>) \<sigma> \<sigma>\<^sub>1 \<Longrightarrow> 
    iterate (eval (program_convert \<Pi>)) (state_convert \<Pi> \<sigma>) (state_convert \<Pi> \<sigma>\<^sub>1)"
  proof (induction "eval_assembly \<Pi>" \<sigma> \<sigma>\<^sub>1 rule: iterate.induct) 
  case iter_refl
    thus ?case by simp
  next case iter_step
    thus ?case by fastforce
  qed

end