theory ParsingCorrectness
imports JackParsing
begin








theorem parse_correct: "complete_jack_parser (program_to_string \<Pi>) = Some \<Pi>"
  apply (induction \<Pi>)
  by simp

end