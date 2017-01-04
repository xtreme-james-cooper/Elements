theory JackParsing
imports "../Parser/Tokenizer" JackLanguage
begin

definition "keywords" :: "string set" where
  "keywords = {''class'', ''constructor'', ''function'', ''method'', ''field'', ''static'', ''var'',
    ''int'', ''char'', ''boolean'', ''void'', ''true'', ''false'', ''null'', ''this'', ''let'', 
    ''do'', ''if'', ''else'', ''while'', ''return''}"

fun get_variable :: "token \<Rightarrow> variable option" where
  "get_variable (Sym s) = (if s \<in> keywords then None else Some s)"
| "get_variable _ = None"

definition variable_parser :: "(token, variable) parser" where
  "variable_parser = deoption (get_variable <$> item)"

definition type_parser :: "(token, type) parser" where
  "type_parser = 
    (\<lambda>_. IntT) <$> constant_parser (Sym ''int'') <|> 
    (\<lambda>_. CharT) <$> constant_parser (Sym ''char'') <|> 
    (\<lambda>_. BoolT) <$> constant_parser (Sym ''boolean'') <|> 
    (\<lambda>v. ObjT v) <$> variable_parser"

datatype subroutine_type = Static | Constructor | Method

definition subroutine_type_parser :: "(token, subroutine_type) parser" where
  "subroutine_type_parser = 
    (\<lambda>x. Static) <$> constant_parser (Sym ''static'') <|> 
    (\<lambda>x. Constructor) <$> constant_parser (Sym ''constructor'') <|> 
    (\<lambda>x. Method) <$> constant_parser (Sym ''method'')"

definition subroutine_parser :: "(token, subroutine_type \<times> variable \<times> subroutine) parser" where
  "subroutine_parser = undefined"

definition class_var_decl_parser :: "(token, bool) parser" where
  "class_var_decl_parser = 
    (\<lambda>x. True) <$> constant_parser (Sym ''static'') <|> 
    (\<lambda>x. False) <$> constant_parser (Sym ''field'')"

definition class_var_parser :: "(token, bool \<times> type \<times> variable list) parser" where
  "class_var_parser = 
    (\<lambda>s t v vs _. (s, t, v # vs)) <$>
    class_var_decl_parser <**>
    type_parser <**>
    variable_parser <**>
    many ((\<lambda>_ v. v) <$> constant_parser Comma <**> variable_parser) <**>
    constant_parser Semicolon"

fun class_vars_to_static :: "(bool \<times> type \<times> variable list) list \<Rightarrow> (variable \<times> type) list" where
  "class_vars_to_static [] = []"
| "class_vars_to_static ((True, t, vs) # vts) = (map (\<lambda>v. (v, t)) vs) @ class_vars_to_static vts"
| "class_vars_to_static ((False, t, vs) # vts) = class_vars_to_static vts"

fun class_vars_to_instance :: "(bool \<times> type \<times> variable list) list \<Rightarrow> (variable \<times> type) list" where
  "class_vars_to_instance [] = []"
| "class_vars_to_instance ((True, t, vs) # vts) = class_vars_to_instance vts"
| "class_vars_to_instance ((False, t, vs) # vts) = 
    (map (\<lambda>v. (v, t)) vs) @ class_vars_to_instance vts"

definition class_parser :: "(token, variable \<times> classdecl) parser" where
  "class_parser = 
    (\<lambda>_ cl _ vs ss _. (cl, 
      classdecl.make (class_vars_to_static vs) 
                     (class_vars_to_instance vs) 
                     (map snd (filter (op = Static o fst) ss))
                     (map snd (filter (op = Constructor o fst) ss))
                     (map snd (filter (op = Method o fst) ss)))) <$> 
    constant_parser (Sym ''class'') <**>
    variable_parser <**>
    constant_parser LCurly <**>
    many class_var_parser <**>
    many subroutine_parser <**>
    constant_parser RCurly"

definition get_main :: "(variable \<times> classdecl) list => statement list option" where
  "get_main cls = 
    Option.bind (map_of cls ''main'') (\<lambda>cl. 
    Option.bind (map_of (staticfuncs cl) ''main'') (\<lambda>subr.
    if outtype subr = UnitT \<and> length (params subr) = 0 then Some (body subr) else None))"

definition program_parser :: "(token, program) parser" where
  "program_parser = 
    deoption ((\<lambda>cls. map_option (\<lambda>main. Program cls main) (get_main cls)) <$> many class_parser)"

definition complete_jack_parser :: "string \<Rightarrow> program option" where
  "complete_jack_parser s = Option.bind (tokenizer s) (map_option fst o program_parser o fst)"

end