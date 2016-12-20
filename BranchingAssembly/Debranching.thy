theory Debranching
imports 
  BranchingAssemblyLanguage 
  "../Assembly/AssemblyLanguage" 
  "../Utilities/Iterate" 
  "../Utilities/FiniteMap"
begin

fun branch_instr_convert :: "code_label set \<Rightarrow> b_assembly list \<Rightarrow> code_label \<Rightarrow> 
    assembly list \<times> code_label \<times> (code_label \<rightharpoonup> assembly list \<times> code_label)" where
  "branch_instr_convert ss [] s = ([], s, empty)"
| "branch_instr_convert ss (ABAssm x # \<pi>) s = (
    let (\<pi>', s', \<Pi>) = branch_instr_convert ss \<pi> s
    in (AAssm x # \<pi>', s', \<Pi>))"
| "branch_instr_convert ss (CBAssm dst cmp # \<pi>) s = (
    let (\<pi>', s', \<Pi>) = branch_instr_convert ss \<pi> s
    in (CAssm dst cmp # \<pi>', s', \<Pi>))"
| "branch_instr_convert ss (IBAssm jmp \<pi>\<^sub>t \<pi>\<^sub>f # \<pi>) s = (
    let s\<^sub>e = new_label ss
    in let (\<pi>\<^sub>t', s\<^sub>t, \<Pi>\<^sub>1) = branch_instr_convert (ss \<union> {s\<^sub>e}) \<pi>\<^sub>t s\<^sub>e
    in let (\<pi>\<^sub>f', s\<^sub>f, \<Pi>\<^sub>2) = branch_instr_convert (ss \<union> dom \<Pi>\<^sub>1 \<union> {s\<^sub>e}) \<pi>\<^sub>f s\<^sub>e
    in let (\<pi>', s', \<Pi>\<^sub>3) = branch_instr_convert (ss \<union> dom \<Pi>\<^sub>1 \<union> dom \<Pi>\<^sub>2 \<union> {s\<^sub>e}) \<pi> s
    in (JAssm jmp s\<^sub>t # \<pi>\<^sub>f', s\<^sub>f, \<Pi>\<^sub>1 ++ \<Pi>\<^sub>2 ++ \<Pi>\<^sub>3 ++ [s\<^sub>t \<mapsto> (\<pi>\<^sub>t', s\<^sub>t), s\<^sub>e \<mapsto> (\<pi>', s')]))"
| "branch_instr_convert ss (PBAssm # \<pi>) s = (
    let (\<pi>', s', \<Pi>) = branch_instr_convert ss \<pi> s
    in (PAssm # \<pi>', s', \<Pi>))"

fun block_convert :: "code_label set \<Rightarrow> code_label \<times> b_assembly list \<times> code_label \<Rightarrow> 
    assembly_program \<Rightarrow> assembly_program" where
  "block_convert ss (s, \<pi>, s') \<Pi> = (
    let (\<pi>', s'', \<Pi>') = branch_instr_convert (ss \<union> dom \<Pi>) \<pi> s' 
    in \<Pi>'(s \<mapsto> (\<pi>', s'')))"

definition debranch :: "b_assembly_program \<Rightarrow> assembly_program" where
  "debranch \<Pi> = finite_map_fold (block_convert (dom \<Pi>)) empty \<Pi>"

function remove_continuations :: "assembly list \<Rightarrow> code_label \<Rightarrow> assembly_program \<Rightarrow> 
    (assembly list \<times> code_label) set" where
  "\<not> finite (dom \<Pi>) \<Longrightarrow> remove_continuations \<pi> s \<Pi> = {(\<pi>, s)}"
| "finite (dom \<Pi>) \<Longrightarrow> remove_continuations \<pi> s \<Pi> = (case \<Pi> s of 
        Some (\<pi>', s') \<Rightarrow> insert (\<pi>, s) (remove_continuations (\<pi> @ \<pi>') s' (\<Pi>(s := None)))
      | None \<Rightarrow> {(\<pi>, s)})"
  by atomize_elim auto
termination
  by (relation "measure (card o dom o snd o snd)") (auto, meson card_Diff1_less domI)

fun state_convert :: "code_label set \<Rightarrow> b_assembly_state \<Rightarrow> assembly_state set" where
  "state_convert ss (\<mu>, a, d, \<pi>, s, \<omega>) = (
    let (\<pi>', s', \<Pi>') = branch_instr_convert ss \<pi> s
    in {(\<mu>, a, d, \<pi>'', s'', \<omega>) | \<pi>'' s''. (\<pi>'', s'') \<in> remove_continuations \<pi>' s' \<Pi>'})"

(* conversion correctness *)

lemma [simp]: "branch_instr_convert ss \<pi>\<^sub>B s = (\<pi>\<^sub>A, s', \<Pi>) \<Longrightarrow> finite ss \<Longrightarrow> finite (dom \<Pi>)"
  proof (induction ss \<pi>\<^sub>B s arbitrary: \<pi>\<^sub>A s' \<Pi> rule: branch_instr_convert.induct)
  case 1
    thus ?case by auto
  next case 2
    thus ?case by (simp split: prod.splits)
  next case 3
    thus ?case by (simp split: prod.splits)
  next case (4 ss jmp \<pi>\<^sub>B\<^sub>t \<pi>\<^sub>B\<^sub>f \<pi>\<^sub>B s)
    let ?s\<^sub>e = "new_label ss"
    have "finite (dom \<Pi>)"
      proof (cases "branch_instr_convert (ss \<union> {?s\<^sub>e}) \<pi>\<^sub>B\<^sub>t ?s\<^sub>e")
      case (fields \<pi>\<^sub>t' s\<^sub>t \<Pi>\<^sub>1) note F1 = fields
        thus ?thesis
          proof (cases "branch_instr_convert (ss \<union> dom \<Pi>\<^sub>1 \<union> {?s\<^sub>e}) \<pi>\<^sub>B\<^sub>f ?s\<^sub>e")
          case (fields \<pi>\<^sub>f' s\<^sub>f \<Pi>\<^sub>2) note F2 = fields
            thus ?thesis
              proof (cases "branch_instr_convert (ss \<union> dom \<Pi>\<^sub>1 \<union> dom \<Pi>\<^sub>2 \<union> {?s\<^sub>e}) \<pi>\<^sub>B s")
              case (fields \<pi>' s'' \<Pi>\<^sub>3)
                with 4 F1 F2 fields show ?thesis by auto
              qed
          qed
      qed
    thus ?case by simp
  next case 5
    thus ?case by (simp split: prod.splits)
  qed

lemma finite_block_convert: "finite (dom \<Pi>) \<Longrightarrow> finite ss \<Longrightarrow> 
    finite (dom (block_convert ss \<pi> \<Pi>))"
  by (cases \<pi>) (auto split: prod.splits)

lemma [simp]: "finite ss \<Longrightarrow> ss \<supseteq> dom \<Pi> \<Longrightarrow> 
    finite (dom (finite_map_fold (block_convert ss) empty \<Pi>))"
  proof (induction "block_convert ss" "empty :: code_label \<Rightarrow> (assembly list \<times> code_label) option" \<Pi> 
         rule: finite_map_fold.induct)
  case 1
    thus ?case by (metis finite_subset)
  next case 2
    thus ?case by simp
  next case (3 \<Pi>)
    let ?x = "SOME x. x \<in> dom \<Pi>"
    let ?ih = "finite_map_fold (block_convert ss) empty (\<Pi>(?x := None))"
    from 3 have "finite (dom ?ih)" by auto
    with finite_block_convert 3 have "finite (dom (block_convert ss (?x, the (\<Pi> ?x)) ?ih))" by simp
    with 3 show ?case by (simp add: Let_def)
  qed

lemma [simp]: "finite (dom \<Pi>) \<Longrightarrow> finite (dom (debranch \<Pi>))"
  by (simp add: debranch_def)

lemma [simp]: "(\<pi>, s) \<in> remove_continuations \<pi> s \<Pi>"
  by (induction \<pi> s \<Pi> rule: remove_continuations.induct) (simp_all split: option.splits)

lemma remove_cont_extends: "(\<pi>', s') \<in> remove_continuations (\<iota> # \<pi>) s \<Pi> \<Longrightarrow> 
    \<exists>\<pi>''. \<pi>' = \<iota> # \<pi> @ \<pi>'' \<and> (\<pi> @ \<pi>'', s') \<in> remove_continuations \<pi> s \<Pi>"
  proof (induction \<pi> s \<Pi> rule: remove_continuations.induct)
  case 1
    thus ?case by simp
  next case (2 \<Pi> \<pi> s)
    thus ?case
      proof (cases "\<Pi> s")
      case (Some ps)
        with 2 show ?thesis by (cases ps) fastforce
      next case None
        with 2 show ?thesis by simp
      qed
  qed

lemma [simp]: "\<Sigma>\<^sub>A \<in> state_convert ss \<Sigma>\<^sub>B \<Longrightarrow> assembly_output \<Sigma>\<^sub>A = b_assembly_output \<Sigma>\<^sub>B"
  by (induction \<Sigma>\<^sub>B rule: b_assembly_output.induct, induction \<Sigma>\<^sub>A rule: assembly_output.induct) 
     (simp split: prod.splits)

lemma debranch_step: "eval_b_assembly \<Pi> \<Sigma>\<^sub>B = Some \<Sigma>\<^sub>B' \<Longrightarrow> \<Sigma>\<^sub>A \<in> state_convert (dom \<Pi>) \<Sigma>\<^sub>B \<Longrightarrow> 
    \<exists>\<Sigma>\<^sub>A'. \<Sigma>\<^sub>A' \<in> state_convert (dom \<Pi>) \<Sigma>\<^sub>B' \<and> eval_assembly (debranch \<Pi>) \<Sigma>\<^sub>A = Some \<Sigma>\<^sub>A'"
  proof (induction \<Pi> \<Sigma>\<^sub>B rule: eval_b_assembly.induct)
  case (1 \<Pi> \<mu> a d s \<omega>)
    thus ?case
      proof (cases "\<Pi> s")
      case (Some ps)
        thus ?thesis
          proof (cases ps)
          case (Pair \<pi>\<^sub>B s')
            thus ?thesis
              proof (cases "branch_instr_convert (dom \<Pi>) \<pi>\<^sub>B s'")
              case (fields \<pi>\<^sub>A s'' \<Pi>')

            
                have X: "\<Sigma>\<^sub>A' \<in> state_convert (dom \<Pi>) (\<mu>, None, d, \<pi>\<^sub>B, s', \<omega>)" by simp
    
    
                have "(case debranch \<Pi> s of 
      Some (\<pi>', s') \<Rightarrow> Some (\<mu>, None, d, \<pi>', s', \<omega>)
    | None \<Rightarrow> None) = Some \<Sigma>\<^sub>A'" by simp
                with X 1 Some Pair fields show ?thesis by auto
              qed
          qed
      next case None
        with 1 show ?thesis by simp
      qed
  next case (2 \<Pi> \<mu> a d x \<pi>\<^sub>B s \<omega>)
    with remove_cont_extends show ?case by (cases "branch_instr_convert (dom \<Pi>) \<pi>\<^sub>B s") fastforce
  next case (3 \<Pi> \<mu> a d dst cmp \<pi>\<^sub>B s \<omega>)
    thus ?case
      proof (cases "branch_instr_convert (dom \<Pi>) \<pi>\<^sub>B s")
      case (fields \<pi>\<^sub>A s' \<Pi>')
        let ?n = "compute cmp (\<mu> a) a d"
        let ?m = "if M \<in> dst then \<mu>(a := ?n) else \<mu>"
        let ?a = "Some (if A \<in> dst then ?n else a)"
        let ?d = "if D \<in> dst then ?n else d"
        from 3 have SB: "\<Sigma>\<^sub>B' = (?m, ?a, ?d, \<pi>\<^sub>B, s, \<omega>)" by (simp add: Let_def)
        from 3 fields obtain \<pi>\<^sub>A' s'' where SA: "\<Sigma>\<^sub>A = (\<mu>, Some a, d, \<pi>\<^sub>A', s'', \<omega>) \<and> 
          (\<pi>\<^sub>A', s'') \<in> remove_continuations (CAssm dst cmp # \<pi>\<^sub>A) s' \<Pi>'" by fastforce
        with remove_cont_extends obtain \<pi>\<^sub>A'' where P: "\<pi>\<^sub>A' = CAssm dst cmp # \<pi>\<^sub>A @ \<pi>\<^sub>A'' \<and> 
          (\<pi>\<^sub>A @ \<pi>\<^sub>A'', s'') \<in> remove_continuations \<pi>\<^sub>A s' \<Pi>'" by fastforce
        have "eval_assembly (debranch \<Pi>) (\<mu>, Some a, d, CAssm dst cmp # \<pi>\<^sub>A @ \<pi>\<^sub>A'', s'', \<omega>) = 
          Some (?m, ?a, ?d, \<pi>\<^sub>A @ \<pi>\<^sub>A'', s'', \<omega>)" by (simp add: Let_def)
        with 3 SA SB P fields show ?thesis by fastforce
      qed
  next case 4
    thus ?case by simp
  next case (5 \<Pi> \<mu> a d jmp \<pi>\<^sub>B\<^sub>t \<pi>\<^sub>B\<^sub>f \<pi>\<^sub>B s \<omega>)
    let ?s\<^sub>e = "new_label (dom \<Pi>)"
    show ?case
      proof (cases "branch_instr_convert (dom \<Pi> \<union> {?s\<^sub>e}) \<pi>\<^sub>B\<^sub>t ?s\<^sub>e")
      case (fields \<pi>\<^sub>t' s\<^sub>t \<Pi>\<^sub>1) note BE = fields
        thus ?thesis
          proof (cases "branch_instr_convert (dom \<Pi> \<union> dom \<Pi>\<^sub>1 \<union> {?s\<^sub>e}) \<pi>\<^sub>B\<^sub>f ?s\<^sub>e")
          case (fields \<pi>\<^sub>f' s\<^sub>f \<Pi>\<^sub>2) note BF = fields
            thus ?thesis
              proof (cases "branch_instr_convert (dom \<Pi> \<union> dom \<Pi>\<^sub>1 \<union> dom \<Pi>\<^sub>2 \<union> {?s\<^sub>e}) \<pi>\<^sub>B s")
              case (fields \<pi>' s' \<Pi>\<^sub>3)
                thus ?thesis
                  proof (cases "should_jump d jmp")
                  case True
                    from 5 True have SB: "\<Sigma>\<^sub>B' = (\<mu>, a, d, \<pi>\<^sub>B\<^sub>t @ \<pi>\<^sub>B, s, \<omega>)" by simp
                    from 5 have SA: "\<Sigma>\<^sub>A \<in> state_convert (dom \<Pi>) (\<mu>, a, d, IBAssm jmp \<pi>\<^sub>B\<^sub>t \<pi>\<^sub>B\<^sub>f # \<pi>\<^sub>B, s, \<omega>)" by simp
                
            from BE BF fields have "state_convert (dom \<Pi>) (\<mu>, a, d, IBAssm jmp \<pi>\<^sub>B\<^sub>t \<pi>\<^sub>B\<^sub>f # \<pi>\<^sub>B, s, \<omega>) = (
                let (\<pi>', s', \<Pi>') = (JAssm jmp s\<^sub>t # \<pi>\<^sub>f', s\<^sub>f, \<Pi>\<^sub>1 ++ \<Pi>\<^sub>2 ++ \<Pi>\<^sub>3 ++ [s\<^sub>t \<mapsto> (\<pi>\<^sub>t', s\<^sub>t), ?s\<^sub>e \<mapsto> (\<pi>', s')])
                in {(\<mu>, a, d, \<pi>'', s'', \<omega>) | \<pi>'' s''. (\<pi>'', s'') \<in> remove_continuations (JAssm jmp s\<^sub>t # \<pi>\<^sub>f') s\<^sub>f \<Pi>'})" by (simp add: Let_def)
            
                
            
                    have X: "\<Sigma>\<^sub>A' \<in> state_convert (dom \<Pi>) (\<mu>, a, d, \<pi>\<^sub>B\<^sub>t @ \<pi>\<^sub>B, s, \<omega>)" by simp
                
                
                    have "eval_assembly (debranch \<Pi>) \<Sigma>\<^sub>A = Some \<Sigma>\<^sub>A'" by simp
                    with SB SA X show ?thesis by metis
                  next case False
                    from 5 False have SB: "\<Sigma>\<^sub>B' = (\<mu>, a, d, \<pi>\<^sub>B\<^sub>f @ \<pi>\<^sub>B, s, \<omega>)" by fastforce
                    from 5 have "\<Sigma>\<^sub>A \<in> state_convert (dom \<Pi>) (\<mu>, a, d, IBAssm jmp \<pi>\<^sub>B\<^sub>t \<pi>\<^sub>B\<^sub>f # \<pi>\<^sub>B, s, \<omega>)" by simp
                
                
                    have X: "\<Sigma>\<^sub>A' \<in> state_convert (dom \<Pi>) (\<mu>, a, d, \<pi>\<^sub>B\<^sub>f @ \<pi>\<^sub>B, s, \<omega>)" by simp
                
                
                    have "eval_assembly (debranch \<Pi>) \<Sigma>\<^sub>A = Some \<Sigma>\<^sub>A'" by simp
                    with SB X show ?thesis by metis
                  qed
              qed
          qed
      qed
  next case (6 \<Pi> \<mu> a d \<pi>\<^sub>B s \<omega>)
    with remove_cont_extends show ?case by (cases "branch_instr_convert (dom \<Pi>) \<pi>\<^sub>B s") fastforce
  qed 

theorem debranching_correct [simp]: "iterate (eval_b_assembly \<Pi>) \<Sigma>\<^sub>B \<Sigma>\<^sub>B' \<Longrightarrow> 
  \<Sigma>\<^sub>A \<in> state_convert (dom \<Pi>) \<Sigma>\<^sub>B \<Longrightarrow> 
    \<exists>\<Sigma>\<^sub>A'. \<Sigma>\<^sub>A' \<in> state_convert (dom \<Pi>) \<Sigma>\<^sub>B' \<and> iterate (eval_assembly (debranch \<Pi>)) \<Sigma>\<^sub>A \<Sigma>\<^sub>A'"
  proof (induction "eval_b_assembly \<Pi>" \<Sigma>\<^sub>B \<Sigma>\<^sub>B' rule: iterate.induct)
  case iter_refl
    thus ?case by fastforce
  next case (iter_step \<Sigma>\<^sub>B \<Sigma>\<^sub>B' \<Sigma>\<^sub>B'')
    then obtain \<Sigma>\<^sub>A' where S: "\<Sigma>\<^sub>A' \<in> state_convert (dom \<Pi>) \<Sigma>\<^sub>B' \<and> 
      iterate (eval_assembly (debranch \<Pi>)) \<Sigma>\<^sub>A \<Sigma>\<^sub>A'" by blast
    with iter_step debranch_step obtain \<Sigma>\<^sub>A'' where
      "\<Sigma>\<^sub>A'' \<in> state_convert (dom \<Pi>) \<Sigma>\<^sub>B'' \<and> eval_assembly (debranch \<Pi>) \<Sigma>\<^sub>A' = Some \<Sigma>\<^sub>A''" by blast
    with S have "\<Sigma>\<^sub>A'' \<in> state_convert (dom \<Pi>) \<Sigma>\<^sub>B'' \<and> iterate (eval_assembly (debranch \<Pi>)) \<Sigma>\<^sub>A \<Sigma>\<^sub>A''" 
      by fastforce
    thus ?case by blast
  qed

end