theory JackParsing
imports "../Parser/Tokenizer" JackLanguage
begin

primrec option_to_list :: "'a list option \<Rightarrow> 'a list" where
  "option_to_list (Some a) = a"
| "option_to_list None = []"

definition "keywords" :: "string set" where
  "keywords = {''class'', ''constructor'', ''function'', ''method'', ''field'', ''static'', ''var'',
    ''int'', ''char'', ''boolean'', ''void'', ''true'', ''false'', ''null'', ''this'', ''let'', 
    ''do'', ''if'', ''else'', ''while'', ''return''}"

fun get_variable :: "token \<Rightarrow> variable option" where
  "get_variable (Sym s) = (if s \<in> keywords then None else Some s)"
| "get_variable _ = None"

definition variable_parser :: "(token, variable) parser" where
  "variable_parser = deoption (get_variable <$> item)"




definition subr_call_parser :: "(token, expression \<times> variable \<times> expression list) parser" where
  "subr_call_parser = undefined"

definition expression_parser :: "(token, expression) parser" where
  "expression_parser = undefined"







definition index_parser :: "(token, expression + variable) parser" where
  "index_parser =
    (\<lambda>_ x _. Inl x) <$>
    constant_parser LSquare <**>
    expression_parser <**>
    constant_parser RSquare"

definition field_parser :: "(token, expression + variable) parser" where
  "field_parser = 
    (\<lambda>_ x. Inr x) <$>
    constant_parser Period <**>
    variable_parser"

definition lvar_parser :: "(token, lvar) parser" where
  "lvar_parser = 
    (\<lambda>x ls. foldl (\<lambda>lv e. case e of Inl e \<Rightarrow> LIndex lv e | Inr x \<Rightarrow> LField lv x) (LVar x) ls) <$>
    variable_parser <**>
    many (index_parser <|> field_parser)"

definition let_statement_parser :: "(token, statement) parser" where
  "let_statement_parser = 
    (\<lambda>_ x _ e _. Let x e) <$>
    constant_parser (Sym ''let'') <**>
    lvar_parser <**>
    constant_parser Equals <**>
    expression_parser <**>
    constant_parser Semicolon"

definition if_statement_parser :: "(token, statement) parser \<Rightarrow> (token, statement) parser" where
  "if_statement_parser statement_parser =
    (\<lambda>_ _ e _ _ s _ el. If e s (option_to_list el)) <$>
    constant_parser (Sym ''if'') <**>
    constant_parser LParen <**>
    expression_parser <**>
    constant_parser RParen <**>
    constant_parser LCurly <**>
    many statement_parser <**>
    constant_parser RCurly <**>
    optional ((\<lambda>_ _ s _. s) <$>
              constant_parser (Sym ''else'') <**>
              constant_parser LCurly <**>
              many statement_parser <**>
              constant_parser RCurly)"

definition while_statement_parser :: "(token, statement) parser \<Rightarrow> (token, statement) parser" where
  "while_statement_parser statement_parser =
    (\<lambda>_ _ e _ _ s _. While e s) <$>
    constant_parser (Sym ''while'') <**>
    constant_parser LParen <**>
    expression_parser <**>
    constant_parser RParen <**>
    constant_parser LCurly <**>
    many statement_parser <**>
    constant_parser RCurly"

definition do_statement_parser :: "(token, statement) parser" where
  "do_statement_parser = 
    (\<lambda>_ (e, x, es) _. Do e x es) <$>
    constant_parser (Sym ''do'') <**>
    subr_call_parser <**>
    constant_parser Semicolon"

definition return_statement_parser :: "(token, statement) parser" where
  "return_statement_parser = 
    (\<lambda>_ e _. Return e) <$>
    constant_parser (Sym ''return'') <**>
    optional expression_parser <**>
    constant_parser Semicolon"

definition statement_parser :: "(token, statement) parser" where
  "statement_parser = pfix (\<lambda>statement_parser. 
      let_statement_parser <|> 
      if_statement_parser statement_parser <|> 
      while_statement_parser statement_parser <|> 
      do_statement_parser <|> 
      return_statement_parser)"

definition var_type_parser :: "(token, type) parser" where
  "var_type_parser = 
    (\<lambda>_. IntT) <$> constant_parser (Sym ''int'') <|> 
    (\<lambda>_. CharT) <$> constant_parser (Sym ''char'') <|> 
    (\<lambda>_. BoolT) <$> constant_parser (Sym ''boolean'') <|> 
    (\<lambda>v. ObjT v) <$> variable_parser"

definition var_decl_parser :: "(token, (variable \<times> type) list) parser" where
  "var_decl_parser = 
    (\<lambda>_ t v vs _. (v, t) # vs) <$>
    constant_parser (Sym ''var'') <**>
    var_type_parser <**>
    variable_parser <**>
    many ((\<lambda>_ t v. (v, t)) <$>
          constant_parser Comma <**> 
          var_type_parser <**> 
          variable_parser) <**>
    constant_parser Semicolon"

definition parameter_parser :: "(token, (variable \<times> type) list) parser" where
  "parameter_parser = 
    option_to_list <$>
    optional ((\<lambda>t v vs. (v, t) # vs) <$>
              var_type_parser <**>
              variable_parser <**>
              many ((\<lambda>_ t v. (v, t)) <$>
                    constant_parser Comma <**> 
                    var_type_parser <**> 
                    variable_parser))"

definition subr_type_parser :: "(token, type) parser" where
  "subr_type_parser = var_type_parser <|> (\<lambda>_. UnitT) <$> constant_parser (Sym ''void'')"

datatype subroutine_kind = Static | Constructor | Method

definition subroutine_kind_parser :: "(token, subroutine_kind) parser" where
  "subroutine_kind_parser = 
    (\<lambda>x. Static) <$> constant_parser (Sym ''static'') <|> 
    (\<lambda>x. Constructor) <$> constant_parser (Sym ''constructor'') <|> 
    (\<lambda>x. Method) <$> constant_parser (Sym ''method'')"

definition subroutine_parser :: "(token, subroutine_kind \<times> variable \<times> subroutine) parser" where
  "subroutine_parser = 
    (\<lambda>s t x _ ps _ _ ls b _. (s, x, subroutine.make t ps ls b)) <$>
    subroutine_kind_parser <**>
    subr_type_parser <**>
    variable_parser <**>
    constant_parser LParen <**>
    parameter_parser <**>
    constant_parser RParen <**>
    constant_parser LCurly <**>
    var_decl_parser <**>
    many statement_parser <**>
    constant_parser RCurly"

definition class_var_decl_parser :: "(token, bool) parser" where
  "class_var_decl_parser = 
    (\<lambda>x. True) <$> constant_parser (Sym ''static'') <|> 
    (\<lambda>x. False) <$> constant_parser (Sym ''field'')"

definition class_var_parser :: "(token, bool \<times> type \<times> variable list) parser" where
  "class_var_parser = 
    (\<lambda>s t v vs _. (s, t, v # vs)) <$>
    class_var_decl_parser <**>
    var_type_parser <**>
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