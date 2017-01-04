theory Parser
imports Main
begin

(* basic parsers *)

type_synonym ('ch, 'a) parser = "'ch list \<Rightarrow> ('a \<times> 'ch list) option"

primrec item :: "('ch, 'ch) parser" where
  "item [] = None" 
| "item (ch # s) = Some (ch, s)"

fun fmap :: "('a \<Rightarrow> 'b) \<Rightarrow> ('ch, 'a) parser \<Rightarrow> ('ch, 'b) parser" (infix "<$>" 70) where
  "fmap f pa s = (case pa s of Some (a, s') \<Rightarrow> Some (f a, s') | None \<Rightarrow> None)"

fun pure :: "'a \<Rightarrow> ('ch, 'a) parser" where
  "pure a s = Some (a, s)"

fun ap :: "('ch, 'a \<Rightarrow> 'b) parser \<Rightarrow> ('ch, 'a) parser \<Rightarrow> ('ch, 'b) parser" (infixl "<**>" 70) where
  "ap pf pa s = (case pf s of 
      Some (f, s') \<Rightarrow> (case pa s' of 
          Some (a, s'') \<Rightarrow> Some (f a, s'') 
        | None \<Rightarrow> None) 
    | None \<Rightarrow> None)"

fun fail :: "('ch, 'a) parser" where
  "fail s = None"

fun alt :: "('ch, 'a) parser \<Rightarrow> ('ch, 'a) parser \<Rightarrow> ('ch, 'a) parser" (infixl "<|>" 60) where
  "alt a b s = (case a s of Some as \<Rightarrow> Some as | None \<Rightarrow> b s)"

fun sat :: "('ch, 'a) parser \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('ch, 'a) parser" (infixl "where" 65) where
  "sat pa f s = (case pa s of Some (a, s') \<Rightarrow> if f a then Some (a, s') else None | None \<Rightarrow> None)"

function many :: "('ch, 'a) parser \<Rightarrow> ('ch, 'a list) parser" where
  "many pa s = (case pa s of 
      None \<Rightarrow> pure [] s
    | Some (f, s') \<Rightarrow> (
        if length s' < length s 
        then case many pa s' of 
            None \<Rightarrow> pure [] s 
          | Some (a, s'') \<Rightarrow> Some (op # f a, s'')
        else undefined))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(a, s). length s)") auto

(* derived parsers *)

definition constant_parser :: "'ch \<Rightarrow> ('ch, 'ch) parser" where
  "constant_parser ch = item where (op = ch)"

primrec string_parser :: "'ch list \<Rightarrow> ('ch, 'ch list) parser" where
  "string_parser [] = pure []"
| "string_parser (ch # s) = pure (op #) <**> constant_parser ch <**> string_parser s"

definition many1 :: "('ch, 'a) parser \<Rightarrow> ('ch, 'a list) parser" where
  "many1 a = pure (op #) <**> a <**> many a"

definition optional :: "('ch, 'a) parser \<Rightarrow> ('ch, 'a option) parser" where
  "optional a = (Some <$> a) <|> pure None"

definition deoption :: "('ch, 'a option) parser \<Rightarrow> ('ch, 'a) parser" where
  "deoption a = the <$> (a where (\<lambda>x. x \<noteq> None))"

(* parser laws *)

lemma [simp]: "fmap id = id"
  by rule (auto split: option.splits)

lemma [simp]: "fmap f o fmap g = fmap (f o g)"
  by rule (auto split: option.splits)

lemma [simp]: "pure id <**> v = v"
  by (auto split: option.splits)

lemma [simp]: "pure f <**> pure v = pure (f v)"
  by auto

lemma [simp]: "f <**> pure v = pure (\<lambda>x. x v) <**> f"
  by (auto split: option.splits)

lemma [simp]: "f <**> (g <**> x) = pure (op o) <**> f <**> g <**> x"
  by (auto split: option.splits)

lemma [simp]: "g <$> x = pure g <**> x"
  by auto

lemma [simp]: "fail <**> p = fail"
  by auto

lemma [simp]: "p <**> fail = fail"
  by (auto split: option.splits)

lemma [simp]: "fail <|> p = p"
  by auto

lemma [simp]: "p <|> fail = p"
  by (auto split: option.splits)

lemma [simp]: "a <|> (b <|> c) = a <|> b <|> c"
  by (auto split: option.splits)

lemma [simp]: "a <**> (b <|> c) = a <**> b <|> a <**> c"
  by (auto split: option.splits)

lemma [simp]: "pure x where p = (if p x then pure x else fail)"
  by auto

lemma [simp]: "fail where p = fail"
  by auto

lemma [simp]: "many fail = pure []"
  by auto

lemma [simp]: "constant_parser ch (ch # s) = Some (ch, s)"
  by (simp add: constant_parser_def)

lemma [simp]: "ch' \<noteq> ch \<Longrightarrow> constant_parser ch (ch' # s) = None"
  by (simp add: constant_parser_def)

lemma [simp]: "constant_parser ch [] = None"
  by (simp add: constant_parser_def)

lemma [simp]: "string_parser s (s @ t) = Some (s, t)"
  by (induction s arbitrary: t) simp_all

lemma [simp]: "length s = length s' \<Longrightarrow> s \<noteq> s' \<Longrightarrow> string_parser s (s' @ t) = None"
  proof (induction s arbitrary: s' t)
  case Nil
    thus ?case by simp
  next case (Cons ch s)
    then obtain ch' s'' where "s' = ch' # s''" by (metis length_Suc_conv)
    with Cons show ?case by (cases "ch = ch'") simp_all
  qed

lemma [simp]: "length s' < length s \<Longrightarrow> string_parser s s' = None"
  proof (induction s arbitrary: s')
  case Nil
    thus ?case by simp
  next case (Cons ch s)
    thus ?case
      proof (induction s')
      case Nil
        thus ?case by simp
      next case (Cons ch' s')
        thus ?case by (cases "ch = ch'") simp_all
      qed
  qed

lemma [simp]: "p s = Some (a, t) \<Longrightarrow> optional p s = Some (Some a, t)"
  by (simp add: optional_def)

lemma [simp]: "p s = None \<Longrightarrow> optional p s = Some (None, s)"
  by (simp add: optional_def)

lemma [simp]: "p s = Some (Some a, t) \<Longrightarrow> deoption p s = Some (a, t)"
  by (simp add: deoption_def)

lemma [simp]: "p s = Some (None, t) \<Longrightarrow> deoption p s = None"
  by (simp add: deoption_def)

lemma [simp]: "p s = None \<Longrightarrow> deoption p s = None"
  by (simp add: deoption_def)

end