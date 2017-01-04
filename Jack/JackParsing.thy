theory JackParsing
imports "../Parser/Tokenizer" JackLanguage
begin

axiomatization main_var :: variable

definition class_parser :: "(token, variable \<times> classdecl) parser" where
  "class_parser = (\<lambda>x. undefined) <$> constant_parser (Sym ''class'')"

definition get_main :: "(variable \<times> classdecl) list => statement list option" where
  "get_main cls = 
    Option.bind (map_of cls main_var) (\<lambda>cl. 
    Option.bind (map_of (staticfuncs cl) main_var) (\<lambda>subr.
    if outtype subr = UnitT \<and> length (params subr) = 0 then Some (body subr) else None))"

definition program_parser :: "(token, program) parser" where
  "program_parser = 
    deoption ((\<lambda>cls. map_option (\<lambda>main. Program cls main) (get_main cls)) <$> many class_parser)"

definition complete_jack_parser :: "string \<Rightarrow> program option" where
  "complete_jack_parser s = Option.bind (tokenizer s) (map_option fst o program_parser o fst)"

end