theory StackFlattener
imports Main
begin

primrec stack_to_mem :: "int list \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> nat \<Rightarrow> int" where
  "stack_to_mem [] \<mu> k = (if k = 0 then 0 else \<mu> k)"
| "stack_to_mem (i # is) \<mu> k = (
    if k = 0 then 1 + int (length is)
    else if k = Suc (length is) then i
    else stack_to_mem is \<mu> k)"

lemma [simp]: "stack_to_mem \<sigma> \<mu> 0 = int (length \<sigma>)"
  by (induction \<sigma>) simp_all

lemma stack_same: "k > 0 \<Longrightarrow> k \<le> length \<sigma> \<Longrightarrow> stack_to_mem \<sigma> \<mu> k = stack_to_mem \<sigma> \<mu>' k"
  by (induction \<sigma>) simp_all

lemma [simp]: "k > length \<sigma> \<Longrightarrow> stack_to_mem \<sigma> \<mu> k = \<mu> k"
  by (induction \<sigma>) simp_all

lemma [simp]: "(stack_to_mem (a # \<sigma>) \<mu>)(nat (1 + int (length \<sigma>)) := b) = stack_to_mem (b # \<sigma>) \<mu>"
  proof
    fix x
    show "((stack_to_mem (a # \<sigma>) \<mu>)(nat (1 + int (length \<sigma>)) := b)) x = stack_to_mem (b # \<sigma>) \<mu> x" 
      by auto
  qed

lemma [simp]: "(stack_to_mem (i1 # \<sigma>) \<mu>)(0 := int (length \<sigma>)) = 
    stack_to_mem \<sigma> (stack_to_mem (i1 # \<sigma>) \<mu>)"
  proof
    fix x
    show "((stack_to_mem (i1 # \<sigma>) \<mu>)(0 := int (length \<sigma>))) x = 
        stack_to_mem \<sigma> (stack_to_mem (i1 # \<sigma>) \<mu>) x" 
      by (cases "x > length \<sigma>") (simp_all add: stack_same)
  qed

lemma [simp]: "(stack_to_mem (i1 # i2 # \<sigma>) \<mu>)(0 := 1 + int (length \<sigma>)) = 
    stack_to_mem (i2 # \<sigma>) (stack_to_mem (i1 # i2 # \<sigma>) \<mu>)"
  proof
    fix x
    show "((stack_to_mem (i1 # i2 # \<sigma>) \<mu>)(0 := 1 + int (length \<sigma>))) x = 
        stack_to_mem (i2 # \<sigma>) (stack_to_mem (i1 # i2 # \<sigma>) \<mu>) x"
      by (cases "x > length \<sigma>") (simp_all add: stack_same)
  qed

lemma [simp]: "(stack_to_mem \<sigma> \<mu>)(0 := int (length \<sigma>) + 1, nat (int (length \<sigma>) + 1) := d) = 
    stack_to_mem (d # \<sigma>) \<mu>"
  proof
    fix x
    show "((stack_to_mem \<sigma> \<mu>)(0 := int (length \<sigma>) + 1, nat (int (length \<sigma>) + 1) := d)) x = 
        stack_to_mem (d # \<sigma>) \<mu> x" by auto
  qed

lemma [simp]: "n < length \<sigma> \<Longrightarrow> stack_to_mem \<sigma> \<mu> (nat (int (length \<sigma>) - int n)) = \<sigma> ! n"
  proof (induction \<sigma> arbitrary: n)
  case Nil
    thus ?case by simp
  next case Cons
    thus ?case by (induction n) fastforce+
  qed

lemma [simp]: "n < length \<sigma> \<Longrightarrow> (stack_to_mem \<sigma> \<mu>)(nat (int (length \<sigma>) - int n) := d) = 
    stack_to_mem (\<sigma>[n := d]) \<mu>"
  proof
    fix x
    assume "n < length \<sigma>"
    thus "((stack_to_mem \<sigma> \<mu>)(nat (int (length \<sigma>) - int n) := d)) x = stack_to_mem (\<sigma>[n := d]) \<mu> x"
      proof (induction \<sigma> arbitrary: n)
      case Nil
        thus ?case by simp
      next case Cons
        thus ?case by (induction n) fastforce+
      qed
  qed

end