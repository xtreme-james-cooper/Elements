theory Debranching
imports BranchingAssemblyLanguage AssemblyLanguage Iterate
begin

fun branch_instr_convert :: "code_label set \<Rightarrow> branching_assembly list \<Rightarrow> 
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
| "branch_instr_convert ss (JBAssm s # \<pi>) = (
    let (\<pi>', \<Pi>) = branch_instr_convert ss \<pi>
    in (JAssm {EQ, LT, GT} s # \<pi>', \<Pi>))"

definition program_convert :: "branching_assembly_program \<Rightarrow> assembly_program" where
  "program_convert \<Pi> = undefined"

definition state_convert :: "branching_assembly_state \<Rightarrow> assembly_state set" where
  "state_convert \<Sigma> = undefined"

(* conversion correctness *)

lemma eval_debranch_conv [simp]: "eval_branching_assembly \<Pi> \<Sigma>\<^sub>B = Some \<Sigma>\<^sub>B' \<Longrightarrow> 
  \<Sigma>\<^sub>A \<in> state_convert \<Sigma>\<^sub>B \<Longrightarrow>
    \<exists>\<Sigma>\<^sub>A'. \<Sigma>\<^sub>A' \<in> state_convert \<Sigma>\<^sub>B' \<and> iterate (eval_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A \<Sigma>\<^sub>A'"
  by simp

theorem debranching_correct [simp]: "iterate (eval_branching_assembly \<Pi>) \<Sigma>\<^sub>B \<Sigma>\<^sub>B' \<Longrightarrow> 
  \<Sigma>\<^sub>A \<in> state_convert \<Sigma>\<^sub>B \<Longrightarrow> 
    \<exists>\<Sigma>\<^sub>A'. \<Sigma>\<^sub>A' \<in> state_convert \<Sigma>\<^sub>B' \<and> iterate (eval_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A \<Sigma>\<^sub>A'"
  proof (induction "eval_branching_assembly \<Pi>" \<Sigma>\<^sub>B \<Sigma>\<^sub>B' arbitrary: \<Sigma>\<^sub>A rule: iterate.induct)
  case iter_refl
    thus ?case by fastforce
  next case (iter_step \<Sigma>\<^sub>B \<Sigma>\<^sub>B' \<Sigma>\<^sub>B'')
    then obtain \<Sigma>\<^sub>A' where S: "\<Sigma>\<^sub>A' \<in> state_convert \<Sigma>\<^sub>B' \<and> 
      iterate (eval_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A \<Sigma>\<^sub>A'" by blast
    with iter_step eval_debranch_conv obtain \<Sigma>\<^sub>A'' where
        "\<Sigma>\<^sub>A'' \<in> state_convert \<Sigma>\<^sub>B'' \<and> iterate (eval_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A' \<Sigma>\<^sub>A''" 
      by blast
    with S have "\<Sigma>\<^sub>A'' \<in> state_convert \<Sigma>\<^sub>B'' \<and> iterate (eval_assembly (program_convert \<Pi>)) \<Sigma>\<^sub>A \<Sigma>\<^sub>A''" 
      by fastforce
    thus ?case by blast
  qed

end