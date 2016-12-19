theory Debranching
imports BranchingAssemblyLanguage AssemblyLanguage Iterate FiniteMap
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
  "remove_continuations \<pi> s \<Pi> = (
    if finite (dom \<Pi>)
    then case \<Pi> s of 
        Some (\<pi>', s') \<Rightarrow> insert (\<pi>, s) (remove_continuations (\<pi> @ \<pi>') s' (\<Pi>(s := None)))
      | None \<Rightarrow> {(\<pi>, s)}
    else {(\<pi>, s)})"
  by pat_completeness auto
termination
  by (relation "measure (card o dom o snd o snd)") (auto, meson card_Diff1_less domI)

fun state_convert :: "code_label set \<Rightarrow> b_assembly_state \<Rightarrow> assembly_state set" where
  "state_convert ss (\<mu>, a, d, \<pi>, s, \<omega>) = (
    let (\<pi>', s', \<Pi>) = branch_instr_convert ss \<pi> s
    in {(\<mu>, a, d, \<pi>'', s'', \<omega>) | \<pi>'' s''. (\<pi>'', s'') \<in> remove_continuations \<pi>' s' \<Pi>})"

(* conversion correctness *)

lemma [simp]: "branch_instr_convert ss \<pi>\<^sub>B = (\<pi>\<^sub>A, \<Pi>) \<Longrightarrow> finite ss \<Longrightarrow> finite (dom \<Pi>)"
  proof (induction ss \<pi>\<^sub>B arbitrary: \<pi>\<^sub>A \<Pi> rule: branch_instr_convert.induct)
  case 1
    thus ?case by auto
  next case 2
    thus ?case by (simp split: prod.splits)
  next case 3
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
  next case 6
    thus ?case by (simp split: prod.splits)
  qed

lemma finite_block_convert: "finite (dom \<Pi>) \<Longrightarrow> finite ss \<Longrightarrow> 
    finite (dom (block_convert ss (s, \<pi>) \<Pi>))"
  by (cases "branch_instr_convert (ss \<union> dom \<Pi>) \<pi>") auto

lemma [simp]: "finite ss \<Longrightarrow> ss \<supseteq> dom \<Pi> \<Longrightarrow> 
    finite (dom (finite_map_fold (block_convert ss) empty \<Pi>))"
  proof (induction "block_convert ss" "empty :: code_label \<Rightarrow> assembly list option" \<Pi> 
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

lemma [simp]: "\<pi> \<in> jump_join \<pi> \<Pi>"
  by (cases "last \<pi>") (simp_all split: option.splits)

lemma jump_join_a: "\<pi>' \<in> jump_join (AAssm x # \<pi>) \<Pi> \<Longrightarrow> 
    \<exists>\<pi>''. \<pi>' = AAssm x # \<pi>'' \<and> \<pi>'' \<in> jump_join \<pi> \<Pi>"
  proof (induction "AAssm x # \<pi>" \<Pi> rule: jump_join.induct)
  case (1 \<Pi>)
    thus ?case
      proof (cases "finite (dom \<Pi>)")
      case True
        from 1 True have "
            last (AAssm x # \<pi>) = JAssm jmp s \<Longrightarrow>
            jmp = {GT, EQ, LT} \<Longrightarrow>
            \<Pi> s = Some pi \<Longrightarrow>
            butlast (AAssm x # \<pi>) @ pi = AAssm x # \<pi> \<Longrightarrow> \<pi>' \<in> jump_join (AAssm x # \<pi>) (\<Pi>(s := None)) \<Longrightarrow> \<exists>\<pi>''. \<pi>' = AAssm x # \<pi>'' \<and> \<pi>'' \<in> jump_join \<pi> (\<Pi>(s := None))" by simp
        from 1 True have "\<pi>' \<in> (
        case last (AAssm x # \<pi>) of
            JAssm jmp s \<Rightarrow> (
              if jmp = {GT, EQ, LT} 
              then case \<Pi> s of 
                  Some \<pi>' \<Rightarrow> insert (AAssm x # \<pi>) (jump_join (butlast (AAssm x # \<pi>) @ \<pi>') (\<Pi>(s := None)))
                | None \<Rightarrow> {AAssm x # \<pi>} 
              else {AAssm x # \<pi>})
          | _ \<Rightarrow> {AAssm x # \<pi>})" by simp
    
    
        have "\<pi>' = AAssm x # \<pi>'' \<and> \<pi>'' \<in> (
        case last \<pi> of
            JAssm jmp s \<Rightarrow> (
              if jmp = {GT, EQ, LT} 
              then case \<Pi> s of 
                  Some \<pi>' \<Rightarrow> insert \<pi> (jump_join (butlast \<pi> @ \<pi>') (\<Pi>(s := None)))
                | None \<Rightarrow> {\<pi>} 
              else {\<pi>})
          | _ \<Rightarrow> {\<pi>})" by simp
        with True show ?thesis by simp
      next case False
        with 1 show ?thesis by simp
      qed
  qed

lemma [simp]: "\<Sigma>\<^sub>A \<in> state_convert ss \<Sigma>\<^sub>B \<Longrightarrow> assembly_output \<Sigma>\<^sub>A = b_assembly_output \<Sigma>\<^sub>B"
  by (induction \<Sigma>\<^sub>B rule: b_assembly_output.induct, induction \<Sigma>\<^sub>A rule: assembly_output.induct) 
     (simp split: prod.splits)

lemma debranch_step: "eval_b_assembly \<Pi> \<Sigma>\<^sub>B = Some \<Sigma>\<^sub>B' \<Longrightarrow> finite (dom \<Pi>) \<Longrightarrow> 
  \<Sigma>\<^sub>A \<in> state_convert (dom \<Pi>) \<Sigma>\<^sub>B \<Longrightarrow> 
    \<exists>\<Sigma>\<^sub>A'. \<Sigma>\<^sub>A' \<in> state_convert (dom \<Pi>) \<Sigma>\<^sub>B' \<and> iterate (eval_assembly (debranch \<Pi>)) \<Sigma>\<^sub>A \<Sigma>\<^sub>A'"
  proof (induction \<Pi> \<Sigma>\<^sub>B rule: eval_b_assembly.induct)
  case 1
    thus ?case by simp
  next case (2 \<Pi> \<mu> a d x \<pi> \<omega>)
    thus ?case by simp
  next case (3 \<Pi> \<mu> a d dst cmp \<pi> \<omega>)
    thus ?case by simp
  next case 4
    thus ?case by simp
  next case (5 \<Pi> \<mu> a d jmp \<pi>\<^sub>t \<pi>\<^sub>f \<pi> \<omega>)
    thus ?case by simp
  next case (6 \<Pi> \<mu> a d s \<pi> \<omega>)
    thus ?case by simp
  next case (7 \<Pi> \<mu> a d \<pi> \<omega>)
    thus ?case by simp
  qed 

theorem debranching_correct [simp]: "iterate (eval_b_assembly \<Pi>) \<Sigma>\<^sub>B \<Sigma>\<^sub>B' \<Longrightarrow> finite (dom \<Pi>) \<Longrightarrow>
  \<Sigma>\<^sub>A \<in> state_convert (dom \<Pi>) \<Sigma>\<^sub>B \<Longrightarrow> 
    \<exists>\<Sigma>\<^sub>A'. \<Sigma>\<^sub>A' \<in> state_convert (dom \<Pi>) \<Sigma>\<^sub>B' \<and> iterate (eval_assembly (debranch \<Pi>)) \<Sigma>\<^sub>A \<Sigma>\<^sub>A'"
  proof (induction "eval_b_assembly \<Pi>" \<Sigma>\<^sub>B \<Sigma>\<^sub>B' rule: iterate.induct)
  case iter_refl
    thus ?case by fastforce
  next case (iter_step \<Sigma>\<^sub>B \<Sigma>\<^sub>B' \<Sigma>\<^sub>B'')
    then obtain \<Sigma>\<^sub>A' where S: "\<Sigma>\<^sub>A' \<in> state_convert (dom \<Pi>) \<Sigma>\<^sub>B' \<and> 
      iterate (eval_assembly (debranch \<Pi>)) \<Sigma>\<^sub>A \<Sigma>\<^sub>A'" by blast
    with iter_step debranch_step obtain \<Sigma>\<^sub>A'' where
      "\<Sigma>\<^sub>A'' \<in> state_convert (dom \<Pi>) \<Sigma>\<^sub>B'' \<and> iterate (eval_assembly (debranch \<Pi>)) \<Sigma>\<^sub>A' \<Sigma>\<^sub>A''" by blast
    with S have "\<Sigma>\<^sub>A'' \<in> state_convert (dom \<Pi>) \<Sigma>\<^sub>B'' \<and> iterate (eval_assembly (debranch \<Pi>)) \<Sigma>\<^sub>A \<Sigma>\<^sub>A''" 
      by fastforce
    thus ?case by blast
  qed

end