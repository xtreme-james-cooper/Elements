theory Iterate
imports Main
begin

inductive iterate :: "('a \<rightharpoonup> 'a) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where 
  iter_refl [simp]: "iterate f x x"
| iter_step [simp]: "iterate f x y \<Longrightarrow> f y = Some z \<Longrightarrow> iterate f x z"

inductive iterate_ind :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where 
  iteri_refl [simp]: "iterate_ind f x x"
| iteri_step [simp]: "iterate_ind f x y \<Longrightarrow> f y z \<Longrightarrow> iterate_ind f x z"

lemma iter_one: "f x = Some y \<Longrightarrow> iterate f x y"
  proof -
    assume "f x = Some y"
    moreover have "iterate f x x" by simp
    ultimately show ?thesis by (metis iter_step)
  qed

lemma iter_two: "f x = Some y \<Longrightarrow> f y = Some z \<Longrightarrow> iterate f x z"
  proof -
    assume "f x = Some y"
    moreover assume "f y = Some z"
    moreover have "iterate f x x" by simp
    ultimately show ?thesis by (metis iter_step)
  qed

lemma iter_prestep: "iterate f y z \<Longrightarrow> f x = Some y \<Longrightarrow> iterate f x z"
  by (induction f y z rule: iterate.induct) (simp_all add: iter_one)

lemma iter_many [elim]: "iterate f x y \<Longrightarrow> iterate f y z \<Longrightarrow> iterate f x z"
  proof (induction f x y rule: iterate.induct)
  case iter_refl
    thus ?case by simp
  next case (iter_step f x y w)
    with iter_prestep have "iterate f y z" by fast
    with iter_step show ?case by simp
  qed

end