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

primrec block_convert :: "code_label set \<Rightarrow> code_label \<times> b_assembly list \<Rightarrow> assembly_program \<Rightarrow> 
    assembly_program" where
  "block_convert ss (s, \<pi>) \<Pi> = (let (\<pi>', \<Pi>') = branch_instr_convert (ss \<union> dom \<Pi>) \<pi> in \<Pi>'(s \<mapsto> \<pi>'))"

definition debranch :: "b_assembly_program \<Rightarrow> assembly_program" where
  "debranch \<Pi> = finite_map_fold (block_convert (dom \<Pi>)) empty \<Pi>"

fun state_convert :: "code_label set \<Rightarrow> b_assembly_state \<Rightarrow> assembly_state" where
  "state_convert ss (\<mu>, a, d, \<pi>) = (let (\<pi>', _) = branch_instr_convert ss \<pi> in (\<mu>, a, d, \<pi>'))"

(* conversion correctness *)

lemma [simp]: "branch_instr_convert ss \<pi>\<^sub>B = (\<pi>\<^sub>A, \<Pi>) \<Longrightarrow> finite ss \<Longrightarrow> finite (dom \<Pi>)"
  proof (induction ss \<pi>\<^sub>B arbitrary: \<pi>\<^sub>A \<Pi> rule: branch_instr_convert.induct)
  case 1
    thus ?case by auto
  next case 2
    thus ?case by (simp split: prod.splits)
  next case (3 ss dst cmp \<pi>\<^sub>B)
    thus ?case by (simp split: prod.splits)
  next case (4 ss jmp \<pi>\<^sub>B\<^sub>t \<pi>\<^sub>B\<^sub>f \<pi>\<^sub>B)
    thus ?case
      proof (cases "branch_instr_convert ss \<pi>\<^sub>B\<^sub>t")
      case (Pair \<pi>\<^sub>A\<^sub>t \<Pi>\<^sub>1) note PT = Pair
        thus ?thesis  
          proof (cases "branch_instr_convert (ss \<union> dom \<Pi>\<^sub>1) \<pi>\<^sub>B\<^sub>f")
          case (Pair \<pi>\<^sub>A\<^sub>f \<Pi>\<^sub>2) note PF = Pair
            thus ?thesis
              proof (cases "branch_instr_convert (ss \<union> dom \<Pi>\<^sub>1 \<union> dom \<Pi>\<^sub>2) \<pi>\<^sub>B")
              case (Pair \<pi>\<^sub>A' \<Pi>\<^sub>3)
                let ?s\<^sub>t = "new_label (ss \<union> dom \<Pi>\<^sub>1 \<union> dom \<Pi>\<^sub>2 \<union> dom \<Pi>\<^sub>3)"
                let ?s\<^sub>e = "new_label (ss \<union> dom \<Pi>\<^sub>1 \<union> dom \<Pi>\<^sub>2 \<union> dom \<Pi>\<^sub>3 \<union> {?s\<^sub>t})"
                from 4 PT PF Pair have "finite (dom (\<Pi>\<^sub>1 ++ \<Pi>\<^sub>2 ++ \<Pi>\<^sub>3 ++ 
                  [?s\<^sub>t \<mapsto> \<pi>\<^sub>A\<^sub>t @ [JAssm {EQ, LT, GT} ?s\<^sub>e], ?s\<^sub>e \<mapsto> \<pi>\<^sub>A']))" by simp
                with 4 PT PF Pair show ?thesis by (simp add: Let_def)
              qed
          qed
      qed
  next case 5
    thus ?case by auto
  qed

lemma finite_block_convert: "finite (dom \<Pi>) \<Longrightarrow> finite ss \<Longrightarrow> 
    finite (dom (block_convert ss (s, \<pi>) \<Pi>))"
  by (cases "branch_instr_convert (ss \<union> dom \<Pi>) \<pi>") auto

lemma [simp]: "finite (dom \<Pi>) \<Longrightarrow> finite (dom (debranch \<Pi>))"
  proof (induction "block_convert (dom \<Pi>)" "empty :: code_label \<Rightarrow> assembly list option" \<Pi> 
         rule: finite_map_fold.induct)
  case 1
    thus ?case by simp
  next case 2
    thus ?case by (simp add: debranch_def)
  next case (3 \<Pi>)
    let ?x = "SOME x. x \<in> dom \<Pi>"

    have "finite (dom (debranch \<Pi>))" by simp
    thus ?case by simp
  qed

lemma [simp]: "finite (dom \<Pi>) \<Longrightarrow> \<Pi> s = Some \<pi>\<^sub>B \<Longrightarrow> branch_instr_convert (dom \<Pi>) \<pi>\<^sub>B = (\<pi>\<^sub>A, \<Pi>') \<Longrightarrow> 
    debranch \<Pi> s = Some \<pi>\<^sub>A"
  proof (induction "block_convert (dom \<Pi>)" "empty :: code_label \<Rightarrow> assembly list option" \<Pi> 
         rule: finite_map_fold.induct)
  case 1
    thus ?case by simp
  next case 2
    thus ?case by simp
  next case (3 \<Pi>)
    let ?x = "SOME x. x \<in> dom \<Pi>"

    have "debranch \<Pi> s = Some \<pi>\<^sub>A" by simp
    show ?case by simp
  qed

lemma [simp]: "eval_b_assembly \<Pi> \<Sigma>\<^sub>B = Some \<Sigma>\<^sub>B' \<Longrightarrow> finite (dom \<Pi>) \<Longrightarrow>
    iterate (eval_assembly (debranch \<Pi>)) (state_convert (dom \<Pi>) \<Sigma>\<^sub>B) (state_convert (dom \<Pi>) \<Sigma>\<^sub>B')"
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
  next case (3 \<Pi> \<mu> a d dst cmp \<pi>)
    let ?n = "compute cmp (\<mu> a) a d"
    let ?\<mu> = "if M \<in> dst then \<mu>(a := ?n) else \<mu>"
    let ?a = "Some (if A \<in> dst then ?n else a)"
    let ?d = "if D \<in> dst then ?n else d"
    show ?case
      proof (cases "branch_instr_convert (dom \<Pi>) \<pi>")
      case (Pair \<pi>' \<Pi>')
        hence S: "state_convert (dom \<Pi>) (?\<mu>, ?a, ?d, \<pi>) = (?\<mu>, ?a, ?d, \<pi>')" by simp
        from Pair have S': "state_convert (dom \<Pi>) (\<mu>, Some a, d, CBAssm dst cmp # \<pi>) = 
          (\<mu>, Some a, d, CAssm dst cmp # \<pi>')" by simp
        have "iterate (eval_assembly (debranch \<Pi>)) (\<mu>, Some a, d, CAssm dst cmp # \<pi>') 
          (?\<mu>, ?a, ?d, \<pi>')" by (meson iter_one eval_assembly.simps(3))
        with 3 S S' show ?thesis by (simp add: Let_def)
      qed
  next case 4
    thus ?case by simp
  next case (5 \<Pi> \<mu> a d cmp \<pi>\<^sub>t \<pi>\<^sub>f \<pi>)
    from 5 have "eval_b_assembly \<Pi> (\<mu>, a, d, IBAssm cmp \<pi>\<^sub>t \<pi>\<^sub>f # \<pi>) = Some \<Sigma>\<^sub>B'" by simp
    from 5 have "finite (dom \<Pi>)" by simp



    have "iterate (eval_assembly (debranch \<Pi>)) (state_convert (dom \<Pi>) (\<mu>, a, d, IBAssm cmp \<pi>\<^sub>t \<pi>\<^sub>f # \<pi>)) (state_convert (dom \<Pi>) \<Sigma>\<^sub>B')" by simp
    thus ?case by simp
  next case (6 \<Pi> \<mu> a d s \<pi>)
    thus ?case
      proof (cases "\<Pi> s")
      case (Some \<pi>\<^sub>2)
        thus ?thesis
          proof (cases "branch_instr_convert (dom \<Pi>) \<pi>\<^sub>2")
          case (Pair \<pi>\<^sub>2' \<Pi>')
            hence S: "state_convert (dom \<Pi>) (\<mu>, None, d, \<pi>\<^sub>2) = (\<mu>, None, d, \<pi>\<^sub>2')" by simp
            from Some Pair 6 have "eval_assembly (debranch \<Pi>) (\<mu>, a, d, JAssm {EQ, LT, GT} s # []) = 
              Some (\<mu>, None, d, \<pi>\<^sub>2')" by auto
            hence "iterate (eval_assembly (debranch \<Pi>)) (\<mu>, a, d, [JAssm {EQ, LT, GT} s]) 
              (\<mu>, None, d, \<pi>\<^sub>2')" by (metis iter_one)
            with 6 Some S show ?thesis by simp
          qed
      next case None
        with 6 show ?thesis by simp
      qed
  qed 

theorem debranching_correct [simp]: "iterate (eval_b_assembly \<Pi>) \<Sigma>\<^sub>B \<Sigma>\<^sub>B' \<Longrightarrow> finite (dom \<Pi>) \<Longrightarrow>
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