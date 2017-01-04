theory Parser
imports Main
begin

(* basic parsers *)

type_synonym 'a parser = "string \<Rightarrow> ('a \<times> string) option"

primrec item :: "char parser" where
  "item [] = None" 
| "item (ch # s) = Some (ch, s)"

fun fmap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a parser \<Rightarrow> 'b parser" (infix "<$>" 70) where
  "fmap f pa s = (case pa s of Some (a, s') \<Rightarrow> Some (f a, s') | None \<Rightarrow> None)"

fun pure :: "'a \<Rightarrow> 'a parser" where
  "pure a s = Some (a, s)"

fun ap :: "('a \<Rightarrow> 'b) parser \<Rightarrow> 'a parser \<Rightarrow> 'b parser" (infixl "<**>" 70) where
  "ap pf pa s = (case pf s of 
      Some (f, s') \<Rightarrow> (case pa s' of 
          Some (a, s'') \<Rightarrow> Some (f a, s'') 
        | None \<Rightarrow> None) 
    | None \<Rightarrow> None)"

fun fail :: "'a parser" where
  "fail s = None"

fun alt :: "'a parser \<Rightarrow> 'a parser \<Rightarrow> 'a parser" (infixl "<|>" 60) where
  "alt a b s = (case a s of Some as \<Rightarrow> Some as | None \<Rightarrow> b s)"

fun sat :: "'a parser \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a parser" (infixl "where" 65) where
  "sat pa f s = (case pa s of Some (a, s') \<Rightarrow> if f a then Some (a, s') else None | None \<Rightarrow> None)"

function many :: "'a parser \<Rightarrow> 'a list parser" where
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

definition char_parser :: "char \<Rightarrow> char parser" where
  "char_parser ch = item where (op = ch)"

primrec string_parser :: "string \<Rightarrow> string parser" where
  "string_parser [] = pure []"
| "string_parser (ch # s) = pure (op #) <**> char_parser ch <**> string_parser s"

definition many1 :: "'a parser \<Rightarrow> 'a list parser" where
  "many1 a = pure (op #) <**> a <**> many a"

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

lemma [simp]: "char_parser ch (ch # s) = Some (ch, s)"
  by (simp add: char_parser_def)

lemma [simp]: "ch' \<noteq> ch \<Longrightarrow> char_parser ch (ch' # s) = None"
  by (simp add: char_parser_def)

lemma [simp]: "char_parser ch [] = None"
  by (simp add: char_parser_def)

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

end