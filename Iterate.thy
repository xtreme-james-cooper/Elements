theory Iterate
imports Main
begin

inductive iterate :: "('a \<rightharpoonup> 'a) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where 
  iter_refl [simp]: "iterate f x x"
| iter_step [simp]: "iterate f x y \<Longrightarrow> f y = Some z \<Longrightarrow> iterate f x z"

lemma [elim]: "f x = Some y \<Longrightarrow> iterate f x y"
  proof -
    assume "f x = Some y"
    moreover have "iterate f x x" by simp
    ultimately show "iterate f x y" by (metis iter_step)
  qed

lemma [elim]: "iterate f y z \<Longrightarrow> f x = Some y \<Longrightarrow> iterate f x z"
  by (induction f y z rule: iterate.induct) auto

lemma [elim]: "iterate f x y \<Longrightarrow> iterate f y z \<Longrightarrow> iterate f x z"
  proof (induction f x y rule: iterate.induct)
  case iter_refl
    thus ?case by simp
  next case (iter_step f x y w)
    hence "iterate f y z" by auto
    with iter_step show ?case by simp
  qed

end