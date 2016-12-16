theory Debranching
imports BranchingAssemblyLanguage AssemblyLanguage Iterate FiniteMap
begin

fun branch_instr_convert :: "code_label set \<Rightarrow> b_assembly list \<Rightarrow> 
    assembly list \<times> (code_label \<rightharpoonup> assembly list)" where
  "branch_instr_convert ss [] = ([], empty)"
| "branch_instr_convert ss (ABAssm x # \<pi>) = (
    let (\<pi>', \<Pi>) = branch_instr_convert ss \<pi>
    in (AAssm x # \<pi>', \<Pi>))"
| "branch_instr_convert ss (CBAssm dst cmp # \<pi>) = (
    let (\<pi>', \<Pi>) = branch_instr_convert ss \<pi>
    in (CAssm dst cmp # \<pi>', \<Pi>))"
| "branch_instr_convert ss (IBAssm jmp \<pi>\<^sub>t \<pi>\<^sub>f # \<pi>) = (
    let (\<pi>\<^sub>t', \<Pi>\<^sub>1) = branch_instr_convert ss \<pi>\<^sub>t
    in let (\<pi>\<^sub>f', \<Pi>\<^sub>2) = branch_instr_convert (ss \<union> dom \<Pi>\<^sub>1) \<pi>\<^sub>f
    in let (\<pi>', \<Pi>\<^sub>3) = branch_instr_convert (ss \<union> dom \<Pi>\<^sub>1 \<union> dom \<Pi>\<^sub>2) \<pi>
    in let s\<^sub>t = new_label (ss \<union> dom \<Pi>\<^sub>1 \<union> dom \<Pi>\<^sub>2 \<union> dom \<Pi>\<^sub>3)
    in let s\<^sub>e = new_label (ss \<union> dom \<Pi>\<^sub>1 \<union> dom \<Pi>\<^sub>2 \<union> dom \<Pi>\<^sub>3 \<union> {s\<^sub>t})
    in (JAssm jmp s\<^sub>t # \<pi>\<^sub>f' @ [JAssm {EQ, LT, GT} s\<^sub>e], 
        \<Pi>\<^sub>1 ++ \<Pi>\<^sub>2 ++ \<Pi>\<^sub>3 ++ [s\<^sub>t \<mapsto> \<pi>\<^sub>t' @ [JAssm {EQ, LT, GT} s\<^sub>e], s\<^sub>e \<mapsto> \<pi>']))"
| "branch_instr_convert ss (JBAssm s # \<pi>) = ([JAssm {EQ, LT, GT} s], empty)"

primrec block_convert :: "code_label \<times> b_assembly list \<Rightarrow> assembly_program \<Rightarrow> assembly_program" 
    where
  "block_convert (s, \<pi>) \<Pi> = (let (\<pi>', \<Pi>') = branch_instr_convert (dom \<Pi>) \<pi> in \<Pi>'(s \<mapsto> \<pi>'))"

definition debranch :: "b_assembly_program \<Rightarrow> assembly_program" where
  "debranch \<Pi> = finite_map_fold block_convert empty \<Pi>"

fun state_convert :: "code_label set \<Rightarrow> b_assembly_state \<Rightarrow> assembly_state" where
  "state_convert ss (\<mu>, a, d, \<pi>) = (let (\<pi>', _) = branch_instr_convert ss \<pi> in (\<mu>, a, d, \<pi>'))"

(* conversion correctness *)

lemma [simp]: "finite (dom \<Pi>) \<Longrightarrow> finite (dom (debranch \<Pi>))"
  by simp

lemma [simp]: "eval_b_assembly \<Pi> \<Sigma>\<^sub>B = Some \<Sigma>\<^sub>B' \<Longrightarrow> 
    iterate (eval_assembly (program_convert \<Pi>)) 
      (state_convert (dom \<Pi>) \<Sigma>\<^sub>B) (state_convert (dom \<Pi>) \<Sigma>\<^sub>B')"
  proof (induction \<Pi> \<Sigma>\<^sub>B rule: eval_b_assembly.induct)
  case 1
    thus ?case by simp
  next case (2 \<Pi> \<mu> a d x \<pi>)
    thus ?case
      proof (cases "branch_instr_convert (dom \<Pi>) \<pi>")
      case (Pair \<pi>' \<Pi>')
        hence S: "state_convert (dom \<Pi>) (\<mu>, a, d, ABAssm x # \<pi>) = (\<mu>, a, d, AAssm x # \<pi>')" by simp
        from Pair have "state_convert (dom \<Pi>) (\<mu>, Some x, d, \<pi>) = (\<mu>, Some x, d, \<pi>')" by simp
        with 2 S show ?thesis by (simp add: iter_one)
      qed
  next case 3
    thus ?case by simp
  next case 4
    thus ?case by simp
  next case 5
    thus ?case by simp
  next case 6
    thus ?case by simp
  qed 

theorem debranching_correct [simp]: "iterate (eval_b_assembly \<Pi>) \<Sigma>\<^sub>B \<Sigma>\<^sub>B' \<Longrightarrow> 
    iterate (eval_assembly (debranch \<Pi>)) (state_convert (dom \<Pi>) \<Sigma>\<^sub>B) (state_convert (dom \<Pi>) \<Sigma>\<^sub>B')"
  proof (induction "eval_b_assembly \<Pi>" \<Sigma>\<^sub>B \<Sigma>\<^sub>B' rule: iterate.induct)
  case iter_refl
    thus ?case by fastforce
  next case (iter_step \<Sigma>\<^sub>B \<Sigma>\<^sub>B' \<Sigma>\<^sub>B'')
    hence "iterate (eval_assembly (debranch \<Pi>)) 
      (state_convert (dom \<Pi>) \<Sigma>\<^sub>B) (state_convert (dom \<Pi>) \<Sigma>\<^sub>B'')" by fastforce
    thus ?case by blast
  qed

end