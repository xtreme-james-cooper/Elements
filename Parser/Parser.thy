theory Parser
imports Main
begin

(* prelims *)

primrec mapfst :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'c) \<Rightarrow> ('b \<times> 'c)" where
  "mapfst f (a, c) = (f a, c)"

definition mapmapfst :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'c) set \<Rightarrow> ('b \<times> 'c) set" where
  "mapmapfst f = op ` (mapfst f)"

lemma [simp]: "op ` f \<circ> op ` g = op ` (f \<circ> g)"
  by fastforce

lemma [simp]: "mapfst id = id"
  by auto

lemma [simp]: "mapfst f o mapfst g = mapfst (f o g)"
  by auto

lemma [simp]: "fst (mapfst f x) = f (fst x)"
  by (cases x) simp

lemma [simp]: "snd (mapfst f x) = snd x"
  by (cases x) simp

lemma [simp]: "(a, b) \<in> xs \<Longrightarrow> (a v, b) \<in> mapfst (\<lambda>x. x v) ` xs"
  proof -
    assume "(a, b) \<in> xs"
    moreover have "(a v, b) = mapfst (\<lambda>x. x v) (a, b)" by simp
    ultimately show ?thesis by fastforce
  qed

lemma [simp]: "(\<Union>fs \<in> xs. {(fst fs v, snd fs)}) = mapmapfst (\<lambda>x. x v) xs"
  by (auto simp add: mapmapfst_def)

lemma [simp]: "(\<Union>xa \<in> fs. mapmapfst (fst xa) (\<Union>fs \<in> g (snd xa). mapmapfst (fst fs) (x (snd fs)))) =
    (\<Union>xa \<in> mapmapfst op \<circ> fs. \<Union>xa \<in> mapmapfst (fst xa) (g (snd xa)). mapmapfst (fst xa) (x (snd xa)))"
  by (auto simp add: mapmapfst_def) (force+)

(* basic parsers *)

type_synonym 'a parser = "string \<Rightarrow> ('a \<times> string) set"

definition item :: "char parser" where
  "item s = (case s of [] \<Rightarrow> {} | (ch # s') \<Rightarrow>{(ch, s')})"

definition fmap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a parser \<Rightarrow> 'b parser" (infix "<$>" 70) where
  "fmap f af = mapmapfst f o af"

definition pure :: "'a \<Rightarrow> 'a parser" where
  "pure a s = {(a, s)}"

definition ap :: "('a \<Rightarrow> 'b) parser \<Rightarrow> 'a parser \<Rightarrow> 'b parser" (infixl "<**>" 70) where
  "ap ff af = (\<lambda>s. \<Union>fs \<in> ff s. mapmapfst (fst fs) (af (snd fs)))"

definition fail :: "'a parser" where
  "fail s = {}"

definition alt :: "'a parser \<Rightarrow> 'a parser \<Rightarrow> 'a parser" (infixl "<|>" 60) where
  "alt a b s = a s \<union> b s"

definition sat :: "'a parser \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a parser" (infixl "where" 65) where
  "sat a f s = (\<Union>as \<in> a s. if f (fst as) then {as} else {})"

function many :: "'a parser \<Rightarrow> 'a list parser" where
  "many a s = (
      if \<forall>s. \<forall>as \<in> a s. length (snd as) < length s
      then insert ([], s) (\<Union>fs \<in> mapmapfst (op #) (a s). mapmapfst (fst fs) (many a (snd fs)))
      else undefined)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(a, s). length s)") (auto simp add: mapmapfst_def, fastforce)

(* derived parsers *)

definition char :: "char \<Rightarrow> char parser" where
  "char ch = item where (op = ch)"

primrec string :: "string \<Rightarrow> string parser" where
  "string [] = pure []"
| "string (ch # s) = pure (op #) <**> char ch <**> string s"

definition many1 :: "'a parser \<Rightarrow> 'a list parser" where
  "many1 a = pure (op #) <**> a <**> many a"

(* parser laws *)

lemma [simp]: "fmap id = id"
  by (auto simp add: fmap_def mapmapfst_def)

lemma [simp]: "fmap f o fmap g = fmap (f o g)"
  by (auto simp add: fmap_def o_assoc mapmapfst_def)

lemma [simp]: "pure id <**> v = v"
  by (auto simp add: pure_def ap_def mapmapfst_def)

lemma [simp]: "pure f <**> pure v = pure (f v)"
  by (auto simp add: pure_def ap_def mapmapfst_def) 

lemma [simp]: "f <**> pure v = pure (\<lambda>x. x v) <**> f"
  by (auto simp add: pure_def ap_def mapmapfst_def)

lemma [simp]: "f <**> (g <**> x) = pure (op o) <**> f <**> g <**> x"
  by (auto simp add: pure_def ap_def)

lemma [simp]: "g <$> x = pure g <**> x"
  by (auto simp add: fmap_def pure_def ap_def)

lemma [simp]: "fail <**> p = fail"
  by (auto simp add: fail_def ap_def)

lemma [simp]: "p <**> fail = fail"
  by (auto simp add: fail_def ap_def mapmapfst_def)

lemma [simp]: "fail <|> p = p"
  by (auto simp add: fail_def alt_def)

lemma [simp]: "p <|> fail = p"
  by (auto simp add: fail_def alt_def)

lemma [simp]: "a <|> (b <|> c) = a <|> b <|> c"
  by (auto simp add: alt_def)

lemma [simp]: "(a <|> c) <**> b = a <**> b <|> c <**> b"
  by rule (auto simp add: ap_def alt_def)

lemma [simp]: "a <**> (b <|> c) = a <**> b <|> a <**> c"
  by (auto simp add: ap_def alt_def, rule) (auto simp add: alt_def mapmapfst_def)

lemma [simp]: "pure x where p = (if p x then pure x else fail)"
  by (auto simp add: pure_def fail_def sat_def)

lemma [simp]: "fail where p = fail"
  by (auto simp add: fail_def sat_def)

lemma [simp]: "(a <|> b) where p = a where p <|> b where p"
  by (auto simp add: alt_def sat_def)

lemma [simp]: "many fail = pure []"
  proof
    fix s
    have "(
      if \<forall>s. \<forall>as \<in> fail s. length (snd as) < length s
      then insert ([], s) (\<Union>fs \<in> mapmapfst (op #) (fail s). mapmapfst (fst fs) (many fail (snd fs)))
      else undefined) = pure [] s" by (simp add: pure_def fail_def mapmapfst_def del: many.simps)
    thus "many fail s = pure [] s" by simp
  qed

end