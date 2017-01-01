theory JackEvaluation
imports JackLanguage
begin

datatype "value" =
  IntV int
| BoolV bool
| CharV char
| NullV
| ArrayV "value list"
| ObjV "variable \<rightharpoonup> value"

inductive typecheck_value :: "value \<Rightarrow> type \<Rightarrow> bool" where
  [simp]: "typecheck_value (IntV i) IntT"
| [simp]: "typecheck_value (BoolV b) BoolT"
| [simp]: "typecheck_value (CharV b) CharT"
| [simp]: "typecheck_value NullV (ObjT x)"
| [simp]: "\<forall>v \<in> set vs. typecheck_value v t \<Longrightarrow> typecheck_value (ArrayV vs) (ArrayT t)"
| [simp]: "typecheck_value (ObjV fs) (ObjT x)"

inductive eval_binop :: "binop \<Rightarrow> value \<Rightarrow> value \<Rightarrow> value \<Rightarrow> bool" where
  [simp]: "eval_binop Plus (IntV i1) (IntV i2) (IntV (i1 + i2))"
| [simp]: "eval_binop Minus (IntV i1) (IntV i2) (IntV (i1 - i2))"
| [simp]: "eval_binop Times (IntV i1) (IntV i2) (IntV (i1 * i2))"
| [simp]: "eval_binop Div (IntV i1) (IntV i2) (IntV (i1 div i2))"
| [simp]: "eval_binop And (BoolV b1) (BoolV b2) (BoolV (b1 \<and> b2))"
| [simp]: "eval_binop Or (BoolV b1) (BoolV b2) (BoolV (b1 \<or> b2))"
| [simp]: "eval_binop Eq (IntV i1) (IntV i2) (BoolV (i1 = i2))"
| [simp]: "eval_binop Eq (BoolV b1) (BoolV b2) (BoolV (b1 = b2))"
| [simp]: "eval_binop Eq (CharV c1) (CharV c2) (BoolV (c1 = c2))"
| [simp]: "eval_binop Gt (IntV i1) (IntV i2) (BoolV (i1 > i2))"
| [simp]: "eval_binop Lt (IntV i1) (IntV i2) (BoolV (i1 < i2))"

inductive eval_expr :: "(variable \<rightharpoonup> value) \<Rightarrow> value \<Rightarrow> expression \<Rightarrow> value \<Rightarrow> bool" where
  "eval_expr \<Gamma> this (IConst i) (IntV i)"
| "eval_expr \<Gamma> this (BConst b) (BoolV b)"
| "eval_expr \<Gamma> this (CConst c) (CharV c)"
| "\<Gamma> x = Some v \<Longrightarrow> eval_expr \<Gamma> this (Var x) v"
| "eval_expr \<Gamma> this This this"
| "eval_expr \<Gamma> this Null NullV"
| "eval_expr \<Gamma> this e1 (ArrayV vs) \<Longrightarrow> eval_expr \<Gamma> this e2 (IntV n) \<Longrightarrow> 
    eval_expr \<Gamma> this (Index e1 e2) (vs ! nat n)"
| "eval_expr \<Gamma> this e (ObjV fs) \<Longrightarrow> fs x = Some v \<Longrightarrow> eval_expr \<Gamma> this (Field e x) v"
| "eval_expr \<Gamma> this (Call e x es) undefined"
| "eval_expr \<Gamma> this e (IntV i) \<Longrightarrow> eval_expr \<Gamma> this (Negate e) (IntV (-i))"
| "eval_expr \<Gamma> this e (BoolV b) \<Longrightarrow> eval_expr \<Gamma> this (Not e) (BoolV (\<not>b))"
| "eval_expr \<Gamma> this e1 v1 \<Longrightarrow> eval_expr \<Gamma> this e2 v2 \<Longrightarrow> eval_binop b v1 v2 v \<Longrightarrow> 
    eval_expr \<Gamma> this (Binop b e1 e2) v"

(* safety *)

lemma canonical_int [elim]: "typecheck_value v IntT \<Longrightarrow> \<exists>i. v = IntV i"
  by (induction v "IntT" rule: typecheck_value.induct) simp_all

lemma canonical_bool [elim]: "typecheck_value v BoolT \<Longrightarrow> \<exists>b. v = BoolV b"
  by (induction v "BoolT" rule: typecheck_value.induct) simp_all

lemma canonical_char [elim]: "typecheck_value v CharT \<Longrightarrow> \<exists>c. v = CharV c"
  by (induction v "CharT" rule: typecheck_value.induct) simp_all

lemma [simp]: "typecheck_binop b t1 t2 \<Longrightarrow> typecheck_value v1 t1 \<Longrightarrow> typecheck_value v2 t1 \<Longrightarrow> 
    eval_binop b v1 v2 v \<Longrightarrow> typecheck_value v t2"
  proof (induction rule: typecheck_binop.induct)
  case tc_plus
    moreover with canonical_int obtain i1 i2 where "v1 = IntV i1" and "v2 = IntV i2" by blast
    ultimately show ?case apply simp
  next case tc_minus
    thus ?case by simp
  next case tc_times
    thus ?case by simp
  next case tc_div
    thus ?case by simp
  next case tc_and
    thus ?case by simp
  next case tc_or
    thus ?case by simp
  next case tc_eqi
    thus ?case by simp
  next case tc_eqc
    thus ?case by simp
  next case tc_eqb
    thus ?case by simp
  next case tc_gt
    thus ?case by simp
  next case tc_lt
    thus ?case by simp
  qed

end