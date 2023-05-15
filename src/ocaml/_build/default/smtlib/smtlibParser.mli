type token =
  | COMMENT of (string)
  | BINARY of (string)
  | HEX_DECIMAL of (string)
  | DECIMAL of (string)
  | NUMERAL of (string)
  | STRING of (string)
  | SYMBOL of (string)
  | KEYWORD of (string)
  | PAR_OPEN
  | PAR_CLOSE
  | UNDERSCORE
  | AS
  | CMD_SET_LOGIC
  | CMD_SET_INFO
  | CMD_SET_OPTION
  | CMD_DECLARE_SORT
  | CMD_DEFINE_SORT
  | CMD_DECLARE_FUN
  | CMD_DEFINE_FUN
  | CMD_ASSERT
  | CMD_CHECK_SAT
  | CMD_GET_MODEL
  | CMD_EXIT
  | BOOL
  | LET
  | TRUE
  | FALSE
  | EOF

val file :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Ast.file
