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
    in let (\<pi>', s', \<Pi>\<^sub>1) = branch_instr_convert (ss \<union> {s\<^sub>e}) \<pi> s
    in let (\<pi>\<^sub>t', s\<^sub>t, \<Pi>\<^sub>2) = branch_instr_convert (ss \<union> dom \<Pi>\<^sub>1 \<union> {s\<^sub>e}) \<pi>\<^sub>t s\<^sub>e
    in let (\<pi>\<^sub>f', s\<^sub>f, \<Pi>\<^sub>3) = branch_instr_convert (ss \<union> dom \<Pi>\<^sub>1 \<union> dom \<Pi>\<^sub>2 \<union> {s\<^sub>e}) \<pi>\<^sub>f s\<^sub>e
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
    (assembly list \<times> code_label)" where
  "\<not> finite (dom \<Pi>) \<Longrightarrow> remove_continuations \<pi> s \<Pi> = (\<pi>, s)"
| "finite (dom \<Pi>) \<Longrightarrow> remove_continuations \<pi> s \<Pi> = (case \<Pi> s of 
        Some (\<pi>', s') \<Rightarrow> remove_continuations (\<pi> @ \<pi>') s' (\<Pi>(s := None))
      | None \<Rightarrow> (\<pi>, s))"
  by atomize_elim auto
termination
  by (relation "measure (card o dom o snd o snd)") (auto, meson card_Diff1_less domI)

fun state_convert :: "code_label set \<Rightarrow> b_assembly_state \<Rightarrow> assembly_state" where
  "state_convert ss (\<mu>, a, d, \<pi>, s, \<omega>) = (
    let (\<pi>', s', \<Pi>') = branch_instr_convert ss \<pi> s
    in let (\<pi>'', s'') = remove_continuations \<pi>' s' \<Pi>'
    in (\<mu>, a, d, \<pi>'', s'', \<omega>))"

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
      proof (cases "branch_instr_convert (ss \<union> {?s\<^sub>e}) \<pi>\<^sub>B s")
      case (fields \<pi>' s'' \<Pi>\<^sub>1) note F1 = fields
        thus ?thesis
          proof (cases "branch_instr_convert (ss \<union> dom \<Pi>\<^sub>1 \<union> {?s\<^sub>e}) \<pi>\<^sub>B\<^sub>t ?s\<^sub>e")
          case (fields \<pi>\<^sub>t' s\<^sub>t \<Pi>\<^sub>2) note F2 = fields
            thus ?thesis
              proof (cases "branch_instr_convert (ss \<union> dom \<Pi>\<^sub>1 \<union> dom \<Pi>\<^sub>2 \<union> {?s\<^sub>e}) \<pi>\<^sub>B\<^sub>f ?s\<^sub>e")
              case (fields \<pi>\<^sub>f' s\<^sub>f \<Pi>\<^sub>3)
                with 4 F1 F2 show ?thesis by auto
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

lemma [simp]: "remove_continuations \<pi> s \<Pi> = (\<pi>', s') \<Longrightarrow>
    remove_continuations (\<iota> # \<pi>) s \<Pi> = (\<iota> # \<pi>', s')"
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

lemma [simp]: "remove_continuations \<pi> s \<Pi> = (\<pi>', s') \<Longrightarrow>
    remove_continuations (\<pi>\<^sub>2 @ \<pi>) s \<Pi> = (\<pi>\<^sub>2 @ \<pi>', s')"
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

lemma [simp]: "finite ss \<Longrightarrow> ss \<supseteq> dom \<Pi> \<Longrightarrow> \<Pi> s = Some (\<pi>\<^sub>B, s') \<Longrightarrow> 
  branch_instr_convert ss \<pi>\<^sub>B s' = (\<pi>\<^sub>A, s'', \<Pi>') \<Longrightarrow> 
    remove_continuations \<pi>\<^sub>A s'' \<Pi>' = (\<pi>\<^sub>A', s''') \<Longrightarrow> 
      finite_map_fold (block_convert ss) empty \<Pi> s = Some (\<pi>\<^sub>A', s''')"
  proof (induction "block_convert ss" "empty :: code_label \<Rightarrow> (assembly list \<times> code_label) option" \<Pi> 
         rule: finite_map_fold.induct)
  case 1
    thus ?case by (metis finite_subset)
  next case 2
    hence False by simp
    thus ?case by simp
  next case (3 \<Pi>)
    let ?x = "SOME x. x \<in> dom \<Pi>"
    let ?ih = "finite_map_fold (block_convert ss) Map.empty (\<Pi>(?x := None))"
    show ?case
      proof (cases "s = ?x")
      case True
        from 3 have "finite (dom \<Pi>)" by simp
        from 3 have "card (dom \<Pi>) \<noteq> 0" by simp
        from 3 have "
          finite ss \<Longrightarrow>
          dom (\<Pi>(?x := None)) \<subseteq> ss \<Longrightarrow>
          (\<Pi>(?x := None)) s = Some (\<pi>\<^sub>B, s') \<Longrightarrow>
          branch_instr_convert (dom (\<Pi>(?x := None))) \<pi>\<^sub>B s' = (\<pi>\<^sub>A, s'', \<Pi>') \<Longrightarrow>
          remove_continuations \<pi>\<^sub>A s'' \<Pi>' = (\<pi>\<^sub>A', s''') \<Longrightarrow> ?ih s = Some (\<pi>\<^sub>A', s''')" by simp
        from 3 have "finite ss" by simp
        from 3 have "dom \<Pi> \<subseteq> ss" by simp
        from 3 have "\<Pi> s = Some (\<pi>\<^sub>B, s')" by simp
        from 3 have "branch_instr_convert ss \<pi>\<^sub>B s' = (\<pi>\<^sub>A, s'', \<Pi>')" by simp
        from 3 have "remove_continuations \<pi>\<^sub>A s'' \<Pi>' = (\<pi>\<^sub>A', s''')" by simp
    
    
    
        have "(let (\<pi>', s'', \<Pi>') = branch_instr_convert (ss \<union> dom ?ih) \<pi>\<^sub>B s' in \<Pi>'(s \<mapsto> (\<pi>', s''))) s = Some (\<pi>\<^sub>A', s''')" by simp
        with 3 have "block_convert ss (s, the (\<Pi> s)) ?ih s = Some (\<pi>\<^sub>A', s''')" by simp
        with True have "block_convert ss (?x, the (\<Pi> ?x)) ?ih s = Some (\<pi>\<^sub>A', s''')" by simp
        with 3 show ?thesis by (simp add: Let_def)
      next case False
        from 3 have "finite (dom \<Pi>)" by simp
        from 3 have "card (dom \<Pi>) \<noteq> 0" by simp
        from 3 have "
          finite ss \<Longrightarrow>
          dom (\<Pi>(?x := None)) \<subseteq> ss \<Longrightarrow>
          (\<Pi>(?x := None)) s = Some (\<pi>\<^sub>B, s') \<Longrightarrow>
          branch_instr_convert (dom (\<Pi>(?x := None))) \<pi>\<^sub>B s' = (\<pi>\<^sub>A, s'', \<Pi>') \<Longrightarrow>
          remove_continuations \<pi>\<^sub>A s'' \<Pi>' = (\<pi>\<^sub>A', s''') \<Longrightarrow> ?ih s = Some (\<pi>\<^sub>A', s''')" by simp
        from 3 have "finite ss" by simp
        from 3 have "dom \<Pi> \<subseteq> ss" by simp
        from 3 have "\<Pi> s = Some (\<pi>\<^sub>B, s')" by simp
        from 3 have "branch_instr_convert ss \<pi>\<^sub>B s' = (\<pi>\<^sub>A, s'', \<Pi>')" by simp
        from 3 have "remove_continuations \<pi>\<^sub>A s'' \<Pi>' = (\<pi>\<^sub>A', s''')" by simp
    
    
    have "block_convert ss (s, \<pi>, s') ?ih = (
        let (\<pi>', s'', \<Pi>') = branch_instr_convert (ss \<union> dom ?ih) \<pi> s' 
        in \<Pi>'(s \<mapsto> (\<pi>', s'')))" by simp
    
        have "block_convert ss (?x, the (\<Pi> ?x)) ?ih s = Some (\<pi>\<^sub>A', s''')" by simp
        with 3 show ?thesis by (simp add: Let_def)
      qed
  qed

lemma [simp]: "finite (dom \<Pi>) \<Longrightarrow>  \<Pi> s = Some (\<pi>\<^sub>B, s') \<Longrightarrow> 
  branch_instr_convert (dom \<Pi>) \<pi>\<^sub>B s' = (\<pi>\<^sub>A, s'', \<Pi>') \<Longrightarrow> 
    remove_continuations \<pi>\<^sub>A s'' \<Pi>' = (\<pi>\<^sub>A', s''') \<Longrightarrow> debranch \<Pi> s = Some (\<pi>\<^sub>A', s''')"
  by (simp add: debranch_def)

lemma [simp]: "assembly_output (state_convert ss \<Sigma>\<^sub>B) = b_assembly_output \<Sigma>\<^sub>B"
  by (induction \<Sigma>\<^sub>B rule: b_assembly_output.induct) (simp split: prod.splits)

lemma debranch_step: "finite (dom \<Pi>) \<Longrightarrow> eval_b_assembly \<Pi> \<Sigma>\<^sub>B = Some \<Sigma>\<^sub>B' \<Longrightarrow> 
    eval_assembly (debranch \<Pi>) (state_convert (dom \<Pi>) \<Sigma>\<^sub>B) = Some (state_convert (dom \<Pi>) \<Sigma>\<^sub>B')"
  proof (induction \<Pi> \<Sigma>\<^sub>B rule: eval_b_assembly.induct)
  case (1 \<Pi> \<mu> a d s \<omega>)
    then obtain ps where "\<Pi> s = Some ps" by (cases "\<Pi> s") simp_all
    then obtain \<pi>\<^sub>B s' where PS: "\<Pi> s = Some (\<pi>\<^sub>B, s')" by (cases ps) simp
    obtain \<pi>\<^sub>A s'' \<Pi>' where B: "branch_instr_convert (dom \<Pi>) \<pi>\<^sub>B s' = (\<pi>\<^sub>A, s'', \<Pi>')" 
      by (cases "branch_instr_convert (dom \<Pi>) \<pi>\<^sub>B s'") simp
    obtain \<pi>\<^sub>A' s''' where C: "remove_continuations \<pi>\<^sub>A s'' \<Pi>' = (\<pi>\<^sub>A', s''')"
      by (cases "remove_continuations \<pi>\<^sub>A s'' \<Pi>'") simp
    from B C have "state_convert (dom \<Pi>) (\<mu>, None, d, \<pi>\<^sub>B, s', \<omega>) = (\<mu>, None, d, \<pi>\<^sub>A', s''', \<omega>)"
      by simp
    with 1 PS B C show ?case by simp
  next case (2 \<Pi> \<mu> a d x \<pi>\<^sub>B s \<omega>)
    obtain \<pi>\<^sub>A s' \<Pi>' where B: "branch_instr_convert (dom \<Pi>) \<pi>\<^sub>B s = (\<pi>\<^sub>A, s', \<Pi>')"
      by (cases "branch_instr_convert (dom \<Pi>) \<pi>\<^sub>B s") simp
    obtain \<pi>\<^sub>A' s'' where C: "remove_continuations \<pi>\<^sub>A s' \<Pi>' = (\<pi>\<^sub>A', s'')"
      by (cases "remove_continuations \<pi>\<^sub>A s' \<Pi>'") simp
    from B C have A: "state_convert (dom \<Pi>) (\<mu>, a, d, ABAssm x # \<pi>\<^sub>B, s, \<omega>) = 
      (\<mu>, a, d, AAssm x # \<pi>\<^sub>A', s'', \<omega>)" by simp
    from B C have "state_convert (dom \<Pi>) (\<mu>, Some x, d, \<pi>\<^sub>B, s, \<omega>) = (\<mu>, Some x, d, \<pi>\<^sub>A', s'', \<omega>)"
      by simp
    with 2 A show ?case by simp
  next case (3 \<Pi> \<mu> a d dst cmp \<pi>\<^sub>B s \<omega>)
    let ?n = "compute cmp (\<mu> (nat a)) a d"
    let ?m = "if M \<in> dst then \<mu>(nat a := ?n) else \<mu>"
    let ?a = "Some (if A \<in> dst then ?n else a)"
    let ?d = "if D \<in> dst then ?n else d"
    obtain \<pi>\<^sub>A s' \<Pi>' where B: "branch_instr_convert (dom \<Pi>) \<pi>\<^sub>B s = (\<pi>\<^sub>A, s', \<Pi>')"
      by (cases "branch_instr_convert (dom \<Pi>) \<pi>\<^sub>B s") simp
    obtain \<pi>\<^sub>A' s'' where C: "remove_continuations \<pi>\<^sub>A s' \<Pi>' = (\<pi>\<^sub>A', s'')" 
      by (cases "remove_continuations \<pi>\<^sub>A s' \<Pi>'") simp
    from B C have S: "state_convert (dom \<Pi>) (?m, ?a, ?d, \<pi>\<^sub>B, s, \<omega>) = (?m, ?a, ?d, \<pi>\<^sub>A', s'', \<omega>)" 
      by simp
    from B C have "state_convert (dom \<Pi>) (\<mu>, Some a, d, CBAssm dst cmp # \<pi>\<^sub>B, s, \<omega>) = 
      (\<mu>, Some a, d, CAssm dst cmp # \<pi>\<^sub>A', s'', \<omega>)" by simp
    with 3 S show ?case by (simp add: Let_def)
  next case 4
    thus ?case by simp
  next case (5 \<Pi> \<mu> a d jmp \<pi>\<^sub>B\<^sub>t \<pi>\<^sub>B\<^sub>f \<pi>\<^sub>B s \<omega>)    
    let ?s\<^sub>e = "new_label (dom \<Pi>)"
    obtain \<pi>\<^sub>A s' \<Pi>\<^sub>1 where B: "branch_instr_convert (dom \<Pi> \<union> {?s\<^sub>e}) \<pi>\<^sub>B s = (\<pi>\<^sub>A, s', \<Pi>\<^sub>1)" 
      by (cases "branch_instr_convert (dom \<Pi> \<union> {?s\<^sub>e}) \<pi>\<^sub>B s") simp
    obtain \<pi>\<^sub>A\<^sub>t s\<^sub>t \<Pi>\<^sub>2 where BT: "branch_instr_convert (dom \<Pi> \<union> dom \<Pi>\<^sub>1 \<union> {?s\<^sub>e}) \<pi>\<^sub>B\<^sub>t ?s\<^sub>e = (\<pi>\<^sub>A\<^sub>t, s\<^sub>t, \<Pi>\<^sub>2)"
      by (cases "branch_instr_convert (dom \<Pi> \<union> dom \<Pi>\<^sub>1 \<union> {?s\<^sub>e}) \<pi>\<^sub>B\<^sub>t ?s\<^sub>e") simp
    obtain \<pi>\<^sub>A\<^sub>f s\<^sub>f \<Pi>\<^sub>3 where BF: "branch_instr_convert (dom \<Pi> \<union> dom \<Pi>\<^sub>1 \<union> dom \<Pi>\<^sub>2 \<union> {?s\<^sub>e}) \<pi>\<^sub>B\<^sub>f ?s\<^sub>e = 
        (\<pi>\<^sub>A\<^sub>f, s\<^sub>f, \<Pi>\<^sub>3)"
      by (cases "branch_instr_convert (dom \<Pi> \<union> dom \<Pi>\<^sub>1 \<union> dom \<Pi>\<^sub>2 \<union> {?s\<^sub>e}) \<pi>\<^sub>B\<^sub>f ?s\<^sub>e") simp
    let ?\<Pi>' = "\<Pi>\<^sub>1 ++ \<Pi>\<^sub>2 ++ \<Pi>\<^sub>3 ++ [s\<^sub>t \<mapsto> (\<pi>\<^sub>A\<^sub>t, s\<^sub>t), ?s\<^sub>e \<mapsto> (\<pi>\<^sub>A, s')]"
    obtain \<pi>\<^sub>A\<^sub>f' s\<^sub>f' where CF: "remove_continuations \<pi>\<^sub>A\<^sub>f s\<^sub>f ?\<Pi>' = (\<pi>\<^sub>A\<^sub>f', s\<^sub>f')"
      by (cases "remove_continuations \<pi>\<^sub>A\<^sub>f s\<^sub>f ?\<Pi>'") simp
    from BT BF B have BI: "branch_instr_convert (dom \<Pi>) (IBAssm jmp \<pi>\<^sub>B\<^sub>t \<pi>\<^sub>B\<^sub>f # \<pi>\<^sub>B) s = 
        (JAssm jmp s\<^sub>t # \<pi>\<^sub>A\<^sub>f, s\<^sub>f, ?\<Pi>')" by simp
    with CF have SI: "state_convert (dom \<Pi>) (\<mu>, a, d, IBAssm jmp \<pi>\<^sub>B\<^sub>t \<pi>\<^sub>B\<^sub>f # \<pi>\<^sub>B, s, \<omega>) = 
        (\<mu>, a, d, JAssm jmp s\<^sub>t # \<pi>\<^sub>A\<^sub>f', s\<^sub>f', \<omega>)" by simp
    thus ?case
      proof (cases "should_jump d jmp")
      case True



        have "(case debranch \<Pi> s\<^sub>t of Some (\<pi>', s'') \<Rightarrow> Some (\<mu>, None, d, \<pi>', s'', \<omega>) | None \<Rightarrow> None) = Some (state_convert (dom \<Pi>) (\<mu>, None, d, \<pi>\<^sub>B\<^sub>t @ \<pi>\<^sub>B, s, \<omega>))" by simp
        with 5 SI True show ?thesis by auto
      next case False


have "state_convert (dom \<Pi>) (\<mu>, None, d, \<pi>\<^sub>B\<^sub>f @ \<pi>\<^sub>B, s, \<omega>) = (
    let (\<pi>', s', \<Pi>') = branch_instr_convert (dom \<Pi>) (\<pi>\<^sub>B\<^sub>f @ \<pi>\<^sub>B) s
    in let (\<pi>\<^sub>A\<^sub>f', s\<^sub>f') = remove_continuations \<pi>' s' \<Pi>'
    in (\<mu>, None, d, \<pi>\<^sub>A\<^sub>f', s\<^sub>f', \<omega>))" by simp

        have "(\<mu>, None, d, \<pi>\<^sub>A\<^sub>f', s\<^sub>f', \<omega>) = state_convert (dom \<Pi>) (\<mu>, None, d, \<pi>\<^sub>B\<^sub>f @ \<pi>\<^sub>B, s, \<omega>)" by simp
        with 5 SI False show ?thesis by auto
      qed
  next case (6 \<Pi> \<mu> a d \<pi>\<^sub>B s \<omega>)
    obtain \<pi>\<^sub>A s' \<Pi>' where B: "branch_instr_convert (dom \<Pi>) \<pi>\<^sub>B s = (\<pi>\<^sub>A, s', \<Pi>')"
      by (cases "branch_instr_convert (dom \<Pi>) \<pi>\<^sub>B s") simp
    obtain \<pi>\<^sub>A' s'' where C: "remove_continuations \<pi>\<^sub>A s' \<Pi>' = (\<pi>\<^sub>A', s'')"
      by (cases "remove_continuations \<pi>\<^sub>A s' \<Pi>'") simp
    from B C have A: "state_convert (dom \<Pi>) (\<mu>, a, d, PBAssm # \<pi>\<^sub>B, s, \<omega>) = 
      (\<mu>, a, d, PAssm # \<pi>\<^sub>A', s'', \<omega>)" by simp
    from B C have "state_convert (dom \<Pi>) (\<mu>, a, d, \<pi>\<^sub>B, s, d # \<omega>) = (\<mu>, a, d, \<pi>\<^sub>A', s'', d # \<omega>)" 
      by simp
    with 6 A show ?case by simp
  qed 

theorem debranching_correct [simp]: "iterate (eval_b_assembly \<Pi>) \<Sigma>\<^sub>B \<Sigma>\<^sub>B' \<Longrightarrow> finite (dom \<Pi>) \<Longrightarrow> 
    iterate (eval_assembly (debranch \<Pi>)) (state_convert (dom \<Pi>) \<Sigma>\<^sub>B) (state_convert (dom \<Pi>) \<Sigma>\<^sub>B')"
  proof (induction "eval_b_assembly \<Pi>" \<Sigma>\<^sub>B \<Sigma>\<^sub>B' rule: iterate.induct)
  case iter_refl
    thus ?case by auto
  next case iter_step
    with debranch_step show ?case by auto
  qed

end