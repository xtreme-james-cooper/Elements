theory JackLanguage
imports Main
begin

type_synonym variable = string

datatype type = 
  IntT | BoolT | CharT | UnitT 
| ObjT variable
| ArrayT type 
| ArrowT "type list" type

datatype binop = 
  Plus | Minus | Times | Div
| And | Or
| Eq | Lt | Gt

datatype expression =
  IConst int
| BConst bool
| SConst string
| Var variable
| This 
| Null
| Index expression expression 
| Field expression variable 
| Call expression variable "expression list"
| Negate expression
| Not expression
| Binop binop expression expression

datatype lvar =
  LVar variable
| LIndex lvar expression 
| LField lvar variable 

datatype statement = 
  Let lvar expression
| If expression "statement list" "statement list"
| While expression "statement list"
| Do expression variable "expression list"
| Return "expression option"

record subroutine = 
  outtype :: type
  params :: "(variable \<times> type) list"
  locals :: "(variable \<times> type) list"
  body :: "statement list"

record classdecl =
  staticvars :: "(variable \<times> type) list" 
  instancevars :: "(variable \<times> type) list"
  staticfuncs :: "(variable \<times> subroutine) list"
  constructors :: "(variable \<times> subroutine) list"
  instancefuncs :: "(variable \<times> subroutine) list"

datatype program = Program "(variable \<times> classdecl) list" "statement list"

(* printing *)

definition combine_with_space :: "string \<Rightarrow> string \<Rightarrow> string" where
  "combine_with_space s\<^sub>1 s\<^sub>2 = s\<^sub>1 @ ''\<newline>'' @ s\<^sub>2"

definition combine_with_comma :: "string \<Rightarrow> string \<Rightarrow> string" where
  "combine_with_comma s\<^sub>1 s\<^sub>2 = s\<^sub>1 @ '' , '' @ s\<^sub>2"

primrec type_to_string :: "type \<Rightarrow> string" where
  "type_to_string IntT = ''int''"
| "type_to_string BoolT = ''bool''"
| "type_to_string CharT = ''char''"
| "type_to_string UnitT = ''void''"
| "type_to_string (ObjT x) = ''x''"
| "type_to_string (ArrayT t) = ''array of '' @ type_to_string t"
| "type_to_string (ArrowT t1 t2) = 
    foldl combine_with_comma ''['' (map type_to_string t1) @ ''] => '' @ type_to_string t2"

primrec binop_to_string :: "binop \<Rightarrow> string" where
  "binop_to_string Plus = ''+''"
| "binop_to_string Minus = ''-''"
| "binop_to_string Times = ''*''"
| "binop_to_string Div = ''/''"
| "binop_to_string And = ''&''"
| "binop_to_string Or = ''|''"
| "binop_to_string Eq = ''=''"
| "binop_to_string Lt = ''<''"
| "binop_to_string Gt = ''>''"

primrec expression_to_string :: "expression \<Rightarrow> string" where
  "expression_to_string (IConst i) = ''i''"
| "expression_to_string (BConst b) = (if b then ''true'' else ''false'')"
| "expression_to_string (SConst s) = ''\"'' @ s @ ''\"''"
| "expression_to_string (Var x) = x"
| "expression_to_string This = ''this''"
| "expression_to_string Null = ''null''"

primrec lvar_to_string :: "lvar \<Rightarrow> string" where
  "lvar_to_string (LVar x) = x"

primrec statement_to_string :: "statement \<Rightarrow> string" where
  "statement_to_string (Let x e) = ''let '' @ lvar_to_string x @ '' = '' @ expression_to_string e"

fun subroutine_to_string :: "subroutine \<Rightarrow> string" where
  "subroutine_to_string \<lparr> outtype = out, params = ps, locals = ls, body = b \<rparr> = undefined"

primrec vardecl_to_string :: "(variable \<times> type) \<Rightarrow> string" where
  "vardecl_to_string (x, t) = type_to_string t @ '' '' @ x"

fun classdecl_to_string :: "(variable \<times> classdecl) \<Rightarrow> string" where
  "classdecl_to_string (name, cl) = ''class { '' @ undefined @ ''}''"

primrec program_to_string :: "program \<Rightarrow> string" where
  "program_to_string (Program classes main) = 
    foldl combine_with_space [] (map classdecl_to_string classes)"

end