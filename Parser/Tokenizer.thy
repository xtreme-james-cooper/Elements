theory Tokenizer
imports Parser
begin

definition ascii :: "char \<Rightarrow> nat" where
  "ascii ch = (THE i. Enum.enum ! i = ch)"

definition is_letter :: "char \<Rightarrow> bool" where
  "is_letter ch = ((ascii ch \<ge> 65 \<and> ascii ch \<le> 90) \<or> (ascii ch \<ge> 97 \<and> ascii ch \<le> 122))"

definition is_digit :: "char \<Rightarrow> bool" where
  "is_digit ch = (ascii ch \<ge> 48 \<and> ascii ch \<le> 57)"

definition char_to_nat :: "char \<Rightarrow> nat" where
  "char_to_nat ch = (if is_digit ch then ascii ch - 48 else undefined)"

definition is_whitespace :: "char \<Rightarrow> bool" where
  "is_whitespace ch = ((ascii ch \<ge> 9 \<and> ascii ch \<le> 13) \<or> ascii ch = 32)"

datatype token = 
  Sym string
| Num nat
| String string
| LCurly | RCurly | LParen | RParen | LSquare | RSquare | Period | Comma | Semicolon | Plus | Hyphen
| Star | Slash | Ampersand | Pipe | LAngle | RAngle | Equals | Tilde

definition symbol_parser :: "(char, string) parser" where
  "symbol_parser = 
    (op #) <$> 
    (item where is_letter) <**> 
    many (item where (\<lambda>ch. is_letter ch \<or> is_digit ch \<or> ch = CHR ''_''))"

definition string_to_nat :: "string \<Rightarrow> nat" where
  "string_to_nat = foldl (\<lambda>n ch. n * 10 + char_to_nat ch) 0"

definition number_parser :: "(char, nat) parser" where
  "number_parser = string_to_nat <$> many1 (item where is_digit)"

definition string_constant_parser :: "(char, string) parser" where
  "string_constant_parser = 
    (\<lambda>ch1 s ch2. s) <$> 
    constant_parser CHR ''\"'' <**> 
    many (item where (\<lambda>ch. ch \<noteq> CHR ''\"'')) <**> 
    constant_parser CHR ''\"''"

definition other_parser :: "(char, token) parser" where
  "other_parser = 
    ((\<lambda>x. LCurly) <$> constant_parser CHR ''{'') <|>
    ((\<lambda>x. RCurly) <$> constant_parser CHR ''}'') <|>
    ((\<lambda>x. LParen) <$> constant_parser CHR ''('') <|>
    ((\<lambda>x. RParen) <$> constant_parser CHR '')'') <|>
    ((\<lambda>x. LSquare) <$> constant_parser CHR ''['') <|>
    ((\<lambda>x. RSquare) <$> constant_parser CHR '']'') <|>
    ((\<lambda>x. Period) <$> constant_parser CHR ''.'') <|>
    ((\<lambda>x. Comma) <$> constant_parser CHR '','') <|>
    ((\<lambda>x. Semicolon) <$> constant_parser CHR '';'') <|>
    ((\<lambda>x. Plus) <$> constant_parser CHR ''+'') <|>
    ((\<lambda>x. Hyphen) <$> constant_parser CHR ''-'') <|>
    ((\<lambda>x. Star) <$> constant_parser CHR ''*'') <|>
    ((\<lambda>x. Slash) <$> constant_parser CHR ''/'') <|>
    ((\<lambda>x. Ampersand) <$> constant_parser CHR ''&'') <|>
    ((\<lambda>x. Pipe) <$> constant_parser CHR ''|'') <|>
    ((\<lambda>x. LAngle) <$> constant_parser CHR ''<'') <|>
    ((\<lambda>x. RAngle) <$> constant_parser CHR ''>'') <|>
    ((\<lambda>x. Equals) <$> constant_parser CHR ''='') <|>
    ((\<lambda>x. Tilde) <$> constant_parser CHR ''~'')"

definition token_parser :: "(char, token) parser" where
  "token_parser = 
    (Sym <$> symbol_parser) <|> 
    (Num <$> number_parser) <|> 
    (String <$> string_constant_parser) <|>
    other_parser"

definition whitespace_parser :: "(char, unit) parser" where
  "whitespace_parser = (\<lambda>x. ()) <$> optional (item where is_whitespace)"

definition tokenizer :: "(char, token list) parser" where
  "tokenizer = 
    (\<lambda>w t. t) <$> 
    whitespace_parser <**> 
    many ((\<lambda>t w. t) <$> token_parser <**> whitespace_parser)"

end