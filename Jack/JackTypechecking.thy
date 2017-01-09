theory JackTypechecking
imports JackLanguage
begin

inductive typecheck_binop :: "binop \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool" where
  tc_plus [simp]: "typecheck_binop Plus IntT IntT"
| tc_minus [simp]: "typecheck_binop Minus IntT IntT"
| tc_times [simp]: "typecheck_binop Times IntT IntT"
| tc_div [simp]: "typecheck_binop Div IntT IntT"
| tc_and [simp]: "typecheck_binop And BoolT BoolT"
| tc_or [simp]: "typecheck_binop Or BoolT BoolT"
| tc_eqi [simp]: "typecheck_binop Eq IntT BoolT"
| tc_eqc [simp]: "typecheck_binop Eq CharT BoolT"
| tc_eqb [simp]: "typecheck_binop Eq BoolT BoolT"
| tc_gt [simp]: "typecheck_binop Gt IntT BoolT"
| tc_lt [simp]: "typecheck_binop Lt IntT BoolT"

inductive typecheck_expr :: "(variable \<rightharpoonup> type) \<Rightarrow> type \<Rightarrow> expression \<Rightarrow> type \<Rightarrow> bool" where
  "typecheck_expr \<Gamma> this (IConst i) IntT"
| "typecheck_expr \<Gamma> this (BConst b) BoolT"
| "typecheck_expr \<Gamma> this (SConst b) (Array CharT)"
| "\<Gamma> x = Some t \<Longrightarrow> typecheck_expr \<Gamma> this (Var x) t"
| "typecheck_expr \<Gamma> this This this"
| "typecheck_expr \<Gamma> this Null (ObjT tx)"
| "typecheck_expr \<Gamma> this e1 (ArrayT t) \<Longrightarrow> typecheck_expr \<Gamma> this e2 IntT \<Longrightarrow> 
    typecheck_expr \<Gamma> this (Index e1 e2) t"
| "typecheck_expr \<Gamma> this e (ObjT tx) \<Longrightarrow> badbadbad x = Some t \<Longrightarrow> typecheck_expr \<Gamma> this (Field e x) t"
| "typecheck_expr \<Gamma> this e (ObjT tx) \<Longrightarrow> badbadbad x = Some (ArrowT ts t) \<Longrightarrow> 
    \<forall>(e', t') \<in> set (zip es ts). typecheck_expr \<Gamma> this e' t' \<Longrightarrow> 
      typecheck_expr \<Gamma> this (Call e x es) t"
| "typecheck_expr \<Gamma> this e IntT \<Longrightarrow> typecheck_expr \<Gamma> this (Negate e) IntT"
| "typecheck_expr \<Gamma> this e BoolT \<Longrightarrow> typecheck_expr \<Gamma> this (Not e) BoolT"
| "typecheck_binop b t1 t2 \<Longrightarrow> typecheck_expr \<Gamma> this e1 t1 \<Longrightarrow> typecheck_expr \<Gamma> this e2 t1 \<Longrightarrow> 
    typecheck_expr \<Gamma> this (Binop b e1 e2) t2"

inductive typecheck_lval :: "(variable \<rightharpoonup> type) \<Rightarrow> type \<Rightarrow> lvar \<Rightarrow> type \<Rightarrow> bool" where
  "\<Gamma> x = Some t \<Longrightarrow> typecheck_lval \<Gamma> this (LVar x) t"
| "typecheck_lval \<Gamma> this l1 (ArrayT t) \<Longrightarrow> typecheck_expr \<Gamma> this e2 IntT \<Longrightarrow> 
    typecheck_lval \<Gamma> this (LIndex l1 e2) t"
| "typecheck_lval \<Gamma> this e (ObjT tx) \<Longrightarrow> badbadbad x = Some t \<Longrightarrow> typecheck_lval \<Gamma> this (LField e x) t"

inductive typecheck_stmt :: "(variable \<rightharpoonup> type) \<Rightarrow> type \<Rightarrow> type \<Rightarrow> statement \<Rightarrow> bool" where
  "typecheck_lval \<Gamma> this x t \<Longrightarrow> typecheck_expr \<Gamma> this e t \<Longrightarrow> typecheck_stmt \<Gamma> this out (Let x e)"
| "typecheck_expr \<Gamma> this e BoolT \<Longrightarrow> \<forall>s' \<in> set s1. typecheck_stmt \<Gamma> this out s' \<Longrightarrow> 
    \<forall>s' \<in> set s2. typecheck_stmt \<Gamma> this out s' \<Longrightarrow> typecheck_stmt \<Gamma> this out (If e s1 s2)"
| "typecheck_expr \<Gamma> this e BoolT \<Longrightarrow> \<forall>s' \<in> set s. typecheck_stmt \<Gamma> this out s' \<Longrightarrow> 
    typecheck_stmt \<Gamma> this out (While e s)"
| "typecheck_expr \<Gamma> this e (ObjT tx) \<Longrightarrow> badbadbad x = Some (ArrowT ts UnitT) \<Longrightarrow> 
    \<forall>(e', t') \<in> set (zip es ts). typecheck_expr \<Gamma> this e' t' \<Longrightarrow> 
      typecheck_stmt \<Gamma> this out (Do e x es)"
| "typecheck_expr \<Gamma> this e out \<Longrightarrow> typecheck_stmt \<Gamma> this out (Return (Some e))"
| "typecheck_stmt \<Gamma> this UnitT (Return None)"

inductive typecheck_subr :: "(variable \<rightharpoonup> type) \<Rightarrow> type \<Rightarrow> subroutine \<Rightarrow> bool" where
  "\<forall>s \<in> set sts. typecheck_stmt (\<Gamma> ++ map_of ps ++ map_of ls) this t s \<Longrightarrow> 
    typecheck_subr \<Gamma> this \<lparr> outtype = t, params = ps, locals = ls, body = sts \<rparr>"

inductive typecheck_class :: "classdecl \<Rightarrow> bool" where
  "typecheck_class \<lparr> staticvars = svs, instancevars = ivs, staticfuncs = sfs, constructors = cts, instancefuncs = ifs \<rparr>"

inductive typecheck_program :: "program \<Rightarrow> bool" where
  "\<forall>(n, cl) \<in> set classes. typecheck_class cl \<Longrightarrow> \<forall>s \<in> set main. typecheck_stmt \<Gamma> this t s \<Longrightarrow> 
    typecheck_program (Program classes main)"

end