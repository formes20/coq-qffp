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

open Parsing;;
let _ = parse_error;;
# 3 "smtlib/smtlibParser.mly"
	open Ast

# 37 "smtlib/smtlibParser.ml"
let yytransl_const = [|
  265 (* PAR_OPEN *);
  266 (* PAR_CLOSE *);
  267 (* UNDERSCORE *);
  268 (* AS *);
  269 (* CMD_SET_LOGIC *);
  270 (* CMD_SET_INFO *);
  271 (* CMD_SET_OPTION *);
  272 (* CMD_DECLARE_SORT *);
  273 (* CMD_DEFINE_SORT *);
  274 (* CMD_DECLARE_FUN *);
  275 (* CMD_DEFINE_FUN *);
  276 (* CMD_ASSERT *);
  277 (* CMD_CHECK_SAT *);
  278 (* CMD_GET_MODEL *);
  279 (* CMD_EXIT *);
  280 (* BOOL *);
  281 (* LET *);
  282 (* TRUE *);
  283 (* FALSE *);
    0 (* EOF *);
    0|]

let yytransl_block = [|
  257 (* COMMENT *);
  258 (* BINARY *);
  259 (* HEX_DECIMAL *);
  260 (* DECIMAL *);
  261 (* NUMERAL *);
  262 (* STRING *);
  263 (* SYMBOL *);
  264 (* KEYWORD *);
    0|]

let yylhs = "\255\255\
\001\000\002\000\002\000\003\000\003\000\003\000\003\000\003\000\
\003\000\003\000\003\000\003\000\003\000\003\000\010\000\012\000\
\012\000\013\000\008\000\008\000\009\000\009\000\015\000\015\000\
\011\000\011\000\011\000\011\000\018\000\018\000\019\000\019\000\
\020\000\017\000\017\000\014\000\014\000\022\000\022\000\021\000\
\021\000\024\000\005\000\005\000\005\000\006\000\006\000\006\000\
\004\000\004\000\004\000\007\000\007\000\016\000\016\000\016\000\
\016\000\016\000\023\000\026\000\027\000\028\000\029\000\025\000\
\025\000\000\000"

let yylen = "\002\000\
\002\000\000\000\002\000\004\000\004\000\004\000\008\000\008\000\
\004\000\004\000\003\000\003\000\003\000\001\000\006\000\000\000\
\002\000\004\000\001\000\004\000\000\000\002\000\001\000\002\000\
\001\000\001\000\004\000\007\000\001\000\002\000\001\000\002\000\
\004\000\001\000\005\000\001\000\005\000\001\000\001\000\001\000\
\002\000\001\000\001\000\002\000\002\000\001\000\002\000\002\000\
\001\000\001\000\001\000\000\000\002\000\001\000\001\000\001\000\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\001\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\014\000\000\000\066\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\001\000\003\000\049\000\050\000\064\000\065\000\000\000\
\051\000\042\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\062\000\061\000\060\000\059\000\063\000\000\000\
\036\000\000\000\034\000\025\000\026\000\054\000\055\000\056\000\
\057\000\058\000\011\000\012\000\013\000\004\000\005\000\045\000\
\044\000\006\000\048\000\047\000\000\000\000\000\000\000\009\000\
\000\000\000\000\000\000\000\000\000\000\010\000\000\000\000\000\
\000\000\000\000\000\000\019\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\053\000\000\000\000\000\
\022\000\000\000\000\000\000\000\017\000\039\000\000\000\000\000\
\038\000\000\000\000\000\000\000\000\000\030\000\027\000\000\000\
\000\000\000\000\000\000\000\000\000\000\037\000\041\000\035\000\
\000\000\000\000\032\000\007\000\024\000\020\000\008\000\018\000\
\015\000\000\000\000\000\033\000\028\000"

let yydgoto = "\002\000\
\005\000\006\000\007\000\041\000\027\000\029\000\072\000\074\000\
\075\000\034\000\084\000\078\000\079\000\076\000\106\000\044\000\
\045\000\085\000\100\000\101\000\095\000\096\000\046\000\028\000\
\025\000\047\000\048\000\049\000\050\000"

let yysindex = "\014\000\
\023\255\000\000\000\000\119\255\000\000\001\000\023\255\104\255\
\020\255\020\255\104\255\104\255\104\255\007\255\019\255\026\255\
\028\255\000\000\000\000\000\000\000\000\000\000\000\000\034\255\
\000\000\000\000\037\255\015\255\041\255\015\255\021\255\048\255\
\049\255\057\255\000\000\000\000\000\000\000\000\000\000\053\255\
\000\000\058\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\104\255\089\255\060\255\000\000\
\249\254\104\255\100\255\067\255\007\255\000\000\104\255\071\255\
\079\255\089\255\072\255\000\000\104\255\073\255\060\255\047\255\
\074\255\089\255\075\255\007\255\077\255\000\000\089\255\089\255\
\000\000\089\255\089\255\089\255\000\000\000\000\082\255\047\255\
\000\000\083\255\104\255\094\255\075\255\000\000\000\000\098\255\
\089\255\102\255\107\255\108\255\007\255\000\000\000\000\000\000\
\007\255\007\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\109\255\110\255\000\000\000\000"

let yyrindex = "\000\000\
\089\000\000\000\000\000\000\000\000\000\000\000\089\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\111\255\000\000\112\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\026\255\113\255\115\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\026\255\000\000\
\000\000\113\255\000\000\000\000\000\000\000\000\115\255\000\000\
\000\000\000\000\000\000\125\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\133\255\
\000\000\000\000\000\000\000\000\134\255\000\000\000\000\000\000\
\135\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\103\000\000\000\251\255\000\000\000\000\043\000\214\255\
\055\000\000\000\244\255\067\000\000\000\242\255\042\000\007\000\
\108\000\065\000\049\000\000\000\056\000\000\000\203\255\141\000\
\000\000\000\000\000\000\000\000\000\000"

let yytablesize = 152
let yytable = "\043\000\
\018\000\042\000\024\000\066\000\067\000\031\000\032\000\033\000\
\035\000\036\000\037\000\038\000\039\000\020\000\001\000\040\000\
\035\000\036\000\037\000\038\000\039\000\020\000\056\000\003\000\
\059\000\043\000\097\000\026\000\051\000\061\000\021\000\004\000\
\022\000\023\000\057\000\052\000\060\000\053\000\021\000\098\000\
\022\000\023\000\097\000\054\000\104\000\105\000\055\000\107\000\
\108\000\109\000\058\000\038\000\082\000\020\000\043\000\071\000\
\062\000\063\000\088\000\020\000\080\000\065\000\105\000\066\000\
\067\000\071\000\064\000\070\000\077\000\043\000\021\000\091\000\
\022\000\023\000\094\000\083\000\021\000\068\000\022\000\023\000\
\087\000\090\000\092\000\099\000\066\000\020\000\103\000\081\000\
\002\000\066\000\094\000\110\000\112\000\113\000\043\000\020\000\
\121\000\073\000\043\000\043\000\122\000\123\000\021\000\114\000\
\022\000\023\000\020\000\116\000\081\000\019\000\020\000\118\000\
\021\000\086\000\022\000\023\000\119\000\120\000\124\000\125\000\
\043\000\046\000\021\000\021\000\016\000\022\000\023\000\021\000\
\089\000\022\000\023\000\008\000\009\000\010\000\029\000\011\000\
\012\000\013\000\014\000\015\000\016\000\017\000\040\000\031\000\
\023\000\093\000\117\000\069\000\102\000\115\000\030\000\111\000"

let yycheck = "\014\000\
\000\000\014\000\008\000\011\001\012\001\011\000\012\000\013\000\
\002\001\003\001\004\001\005\001\006\001\007\001\001\000\009\001\
\002\001\003\001\004\001\005\001\006\001\007\001\028\000\001\001\
\030\000\040\000\080\000\008\001\010\001\009\001\024\001\009\001\
\026\001\027\001\028\000\010\001\030\000\010\001\024\001\082\000\
\026\001\027\001\096\000\010\001\087\000\088\000\010\001\090\000\
\091\000\092\000\010\001\005\001\067\000\007\001\069\000\061\000\
\009\001\009\001\073\000\007\001\066\000\009\001\105\000\011\001\
\012\001\071\000\010\001\010\001\009\001\084\000\024\001\077\000\
\026\001\027\001\080\000\009\001\024\001\025\001\026\001\027\001\
\010\001\010\001\010\001\009\001\011\001\007\001\010\001\009\001\
\000\000\011\001\096\000\010\001\010\001\099\000\109\000\007\001\
\109\000\009\001\113\000\114\000\113\000\114\000\024\001\010\001\
\026\001\027\001\007\001\010\001\009\001\007\000\007\001\010\001\
\024\001\071\000\026\001\027\001\010\001\010\001\010\001\010\001\
\010\001\010\001\010\001\024\001\010\001\026\001\027\001\024\001\
\074\000\026\001\027\001\013\001\014\001\015\001\010\001\017\001\
\018\001\019\001\020\001\021\001\022\001\023\001\010\001\010\001\
\010\001\079\000\105\000\040\000\084\000\101\000\010\000\096\000"

let yynames_const = "\
  PAR_OPEN\000\
  PAR_CLOSE\000\
  UNDERSCORE\000\
  AS\000\
  CMD_SET_LOGIC\000\
  CMD_SET_INFO\000\
  CMD_SET_OPTION\000\
  CMD_DECLARE_SORT\000\
  CMD_DEFINE_SORT\000\
  CMD_DECLARE_FUN\000\
  CMD_DEFINE_FUN\000\
  CMD_ASSERT\000\
  CMD_CHECK_SAT\000\
  CMD_GET_MODEL\000\
  CMD_EXIT\000\
  BOOL\000\
  LET\000\
  TRUE\000\
  FALSE\000\
  EOF\000\
  "

let yynames_block = "\
  COMMENT\000\
  BINARY\000\
  HEX_DECIMAL\000\
  DECIMAL\000\
  NUMERAL\000\
  STRING\000\
  SYMBOL\000\
  KEYWORD\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'script) in
    Obj.repr(
# 22 "smtlib/smtlibParser.mly"
                                        ( _1 )
# 244 "smtlib/smtlibParser.ml"
               : Ast.file))
; (fun __caml_parser_env ->
    Obj.repr(
# 26 "smtlib/smtlibParser.mly"
                                        ( [] )
# 250 "smtlib/smtlibParser.ml"
               : 'script))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'command) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'script) in
    Obj.repr(
# 27 "smtlib/smtlibParser.mly"
                                        ( _1::_2 )
# 258 "smtlib/smtlibParser.ml"
               : 'script))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'symbol) in
    Obj.repr(
# 35 "smtlib/smtlibParser.mly"
                                     ( CSetLogic _3 )
# 265 "smtlib/smtlibParser.ml"
               : 'command))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'attribute) in
    Obj.repr(
# 37 "smtlib/smtlibParser.mly"
                                     ( CSetInfo _3 )
# 272 "smtlib/smtlibParser.ml"
               : 'command))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'solver_option) in
    Obj.repr(
# 39 "smtlib/smtlibParser.mly"
                                     ( CSetOption _3 )
# 279 "smtlib/smtlibParser.ml"
               : 'command))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : 'symbol) in
    let _5 = (Parsing.peek_val __caml_parser_env 3 : 'symbol_list) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'sort) in
    Obj.repr(
# 41 "smtlib/smtlibParser.mly"
                                      ( CDefineSort (_3, _5, _7))
# 288 "smtlib/smtlibParser.ml"
               : 'command))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : 'symbol) in
    let _5 = (Parsing.peek_val __caml_parser_env 3 : 'sort_list) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'sort) in
    Obj.repr(
# 43 "smtlib/smtlibParser.mly"
                                        ( CDeclareFun (_3, _5, _7) )
# 297 "smtlib/smtlibParser.ml"
               : 'command))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'function_def) in
    Obj.repr(
# 45 "smtlib/smtlibParser.mly"
                                        ( let (a, b, c, d) = _3 in
 										  CDefineFun (a, b, c, d) )
# 305 "smtlib/smtlibParser.ml"
               : 'command))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 47 "smtlib/smtlibParser.mly"
                                        ( CAssert _3 )
# 312 "smtlib/smtlibParser.ml"
               : 'command))
; (fun __caml_parser_env ->
    Obj.repr(
# 48 "smtlib/smtlibParser.mly"
                                        ( CCheckSat )
# 318 "smtlib/smtlibParser.ml"
               : 'command))
; (fun __caml_parser_env ->
    Obj.repr(
# 49 "smtlib/smtlibParser.mly"
                                        ( CGetModel )
# 324 "smtlib/smtlibParser.ml"
               : 'command))
; (fun __caml_parser_env ->
    Obj.repr(
# 50 "smtlib/smtlibParser.mly"
                                        ( CExit )
# 330 "smtlib/smtlibParser.ml"
               : 'command))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 51 "smtlib/smtlibParser.mly"
                                        ( CComment _1 )
# 337 "smtlib/smtlibParser.ml"
               : 'command))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : 'symbol) in
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'sorted_var_list) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'sort) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 56 "smtlib/smtlibParser.mly"
                                        ( (_1, _3, _5, _6) )
# 347 "smtlib/smtlibParser.ml"
               : 'function_def))
; (fun __caml_parser_env ->
    Obj.repr(
# 60 "smtlib/smtlibParser.mly"
                                        ( [] )
# 353 "smtlib/smtlibParser.ml"
               : 'sorted_var_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'sorted_var) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'sorted_var_list) in
    Obj.repr(
# 61 "smtlib/smtlibParser.mly"
                                        ( _1::_2 )
# 361 "smtlib/smtlibParser.ml"
               : 'sorted_var_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'symbol) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'sort) in
    Obj.repr(
# 65 "smtlib/smtlibParser.mly"
                                        ( (_2, _3) )
# 369 "smtlib/smtlibParser.ml"
               : 'sorted_var))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'identifier) in
    Obj.repr(
# 71 "smtlib/smtlibParser.mly"
                                        ( SIdentifier _1 )
# 376 "smtlib/smtlibParser.ml"
               : 'sort))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'identifier) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'sort_list_nonempty) in
    Obj.repr(
# 73 "smtlib/smtlibParser.mly"
                                     ( SApplication (_2, _3) )
# 384 "smtlib/smtlibParser.ml"
               : 'sort))
; (fun __caml_parser_env ->
    Obj.repr(
# 77 "smtlib/smtlibParser.mly"
                                        ( [] )
# 390 "smtlib/smtlibParser.ml"
               : 'sort_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'sort) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'sort_list) in
    Obj.repr(
# 78 "smtlib/smtlibParser.mly"
                                        ( _1::_2 )
# 398 "smtlib/smtlibParser.ml"
               : 'sort_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'sort) in
    Obj.repr(
# 82 "smtlib/smtlibParser.mly"
                                        ( [_1] )
# 405 "smtlib/smtlibParser.ml"
               : 'sort_list_nonempty))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'sort) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'sort_list_nonempty) in
    Obj.repr(
# 83 "smtlib/smtlibParser.mly"
                                        ( _1::_2 )
# 413 "smtlib/smtlibParser.ml"
               : 'sort_list_nonempty))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'spec_constant) in
    Obj.repr(
# 90 "smtlib/smtlibParser.mly"
                                        ( TConstant _1 )
# 420 "smtlib/smtlibParser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'qual_identifier) in
    Obj.repr(
# 91 "smtlib/smtlibParser.mly"
                                        ( TVariable _1 )
# 427 "smtlib/smtlibParser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'qual_identifier) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'term_list_nontmpey) in
    Obj.repr(
# 93 "smtlib/smtlibParser.mly"
                                     ( TApplication (_2, _3) )
# 435 "smtlib/smtlibParser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 3 : 'var_binding_list_nonempty) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 95 "smtlib/smtlibParser.mly"
                                        ( TLet (_4, _6) )
# 443 "smtlib/smtlibParser.ml"
               : 'term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'term) in
    Obj.repr(
# 99 "smtlib/smtlibParser.mly"
                                        ( [_1] )
# 450 "smtlib/smtlibParser.ml"
               : 'term_list_nontmpey))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'term_list_nontmpey) in
    Obj.repr(
# 100 "smtlib/smtlibParser.mly"
                                        ( _1::_2 )
# 458 "smtlib/smtlibParser.ml"
               : 'term_list_nontmpey))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'var_binding) in
    Obj.repr(
# 107 "smtlib/smtlibParser.mly"
                                        ( [_1] )
# 465 "smtlib/smtlibParser.ml"
               : 'var_binding_list_nonempty))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'var_binding) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'var_binding_list_nonempty) in
    Obj.repr(
# 109 "smtlib/smtlibParser.mly"
                                        ( _1::_2 )
# 473 "smtlib/smtlibParser.ml"
               : 'var_binding_list_nonempty))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'symbol) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'term) in
    Obj.repr(
# 113 "smtlib/smtlibParser.mly"
                                        ( (_2, _3) )
# 481 "smtlib/smtlibParser.ml"
               : 'var_binding))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'identifier) in
    Obj.repr(
# 120 "smtlib/smtlibParser.mly"
                                        ( QIdentifier _1 )
# 488 "smtlib/smtlibParser.ml"
               : 'qual_identifier))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'identifier) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'sort) in
    Obj.repr(
# 122 "smtlib/smtlibParser.mly"
                                        ( QAnnotated (_3, _4) )
# 496 "smtlib/smtlibParser.ml"
               : 'qual_identifier))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'symbol) in
    Obj.repr(
# 126 "smtlib/smtlibParser.mly"
                                        ( ISimple _1 )
# 503 "smtlib/smtlibParser.ml"
               : 'identifier))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'symbol) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'index_list_nonempty) in
    Obj.repr(
# 128 "smtlib/smtlibParser.mly"
                                        ( IIndexed (_3, _4) )
# 511 "smtlib/smtlibParser.ml"
               : 'identifier))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'numeral) in
    Obj.repr(
# 132 "smtlib/smtlibParser.mly"
                                        ( INumeral _1 )
# 518 "smtlib/smtlibParser.ml"
               : 'index))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'symbol) in
    Obj.repr(
# 133 "smtlib/smtlibParser.mly"
                                        ( ISymbol _1 )
# 525 "smtlib/smtlibParser.ml"
               : 'index))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'index) in
    Obj.repr(
# 137 "smtlib/smtlibParser.mly"
                                        ( [_1] )
# 532 "smtlib/smtlibParser.ml"
               : 'index_list_nonempty))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'index) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'index_list_nonempty) in
    Obj.repr(
# 138 "smtlib/smtlibParser.mly"
                                        ( _1::_2 )
# 540 "smtlib/smtlibParser.ml"
               : 'index_list_nonempty))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 146 "smtlib/smtlibParser.mly"
                                        ( _1 )
# 547 "smtlib/smtlibParser.ml"
               : 'keyword))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'keyword) in
    Obj.repr(
# 150 "smtlib/smtlibParser.mly"
                                        ( AKeyword _1 )
# 554 "smtlib/smtlibParser.ml"
               : 'attribute))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'keyword) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'spec_constant) in
    Obj.repr(
# 151 "smtlib/smtlibParser.mly"
                                        ( AConstant (_1, _2) )
# 562 "smtlib/smtlibParser.ml"
               : 'attribute))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'keyword) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'symbol) in
    Obj.repr(
# 152 "smtlib/smtlibParser.mly"
                                        ( ASymbol (_1, _2) )
# 570 "smtlib/smtlibParser.ml"
               : 'attribute))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'keyword) in
    Obj.repr(
# 159 "smtlib/smtlibParser.mly"
                                        ( OKeyword _1 )
# 577 "smtlib/smtlibParser.ml"
               : 'solver_option))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'keyword) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'spec_constant) in
    Obj.repr(
# 160 "smtlib/smtlibParser.mly"
                                        ( OConstant (_1, _2) )
# 585 "smtlib/smtlibParser.ml"
               : 'solver_option))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'keyword) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'symbol) in
    Obj.repr(
# 161 "smtlib/smtlibParser.mly"
                                        ( OSymbol (_1, _2) )
# 593 "smtlib/smtlibParser.ml"
               : 'solver_option))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 168 "smtlib/smtlibParser.mly"
                                        ( _1 )
# 600 "smtlib/smtlibParser.ml"
               : 'symbol))
; (fun __caml_parser_env ->
    Obj.repr(
# 169 "smtlib/smtlibParser.mly"
                                        ( bool_type_name )
# 606 "smtlib/smtlibParser.ml"
               : 'symbol))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'bool_value) in
    Obj.repr(
# 170 "smtlib/smtlibParser.mly"
                                        ( string_of_bool _1 )
# 613 "smtlib/smtlibParser.ml"
               : 'symbol))
; (fun __caml_parser_env ->
    Obj.repr(
# 174 "smtlib/smtlibParser.mly"
                                        ( [] )
# 619 "smtlib/smtlibParser.ml"
               : 'symbol_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'symbol) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'symbol_list) in
    Obj.repr(
# 175 "smtlib/smtlibParser.mly"
                                            ( _1::_2 )
# 627 "smtlib/smtlibParser.ml"
               : 'symbol_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'numeral) in
    Obj.repr(
# 181 "smtlib/smtlibParser.mly"
                                        ( CNumeral _1 )
# 634 "smtlib/smtlibParser.ml"
               : 'spec_constant))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'decimal) in
    Obj.repr(
# 182 "smtlib/smtlibParser.mly"
                                        ( CDecimal _1 )
# 641 "smtlib/smtlibParser.ml"
               : 'spec_constant))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'hexadecimal) in
    Obj.repr(
# 183 "smtlib/smtlibParser.mly"
                                        ( CHexDecimal _1 )
# 648 "smtlib/smtlibParser.ml"
               : 'spec_constant))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'binary) in
    Obj.repr(
# 184 "smtlib/smtlibParser.mly"
                                        ( CBinary _1 )
# 655 "smtlib/smtlibParser.ml"
               : 'spec_constant))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'string) in
    Obj.repr(
# 185 "smtlib/smtlibParser.mly"
                                        ( CString _1 )
# 662 "smtlib/smtlibParser.ml"
               : 'spec_constant))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 189 "smtlib/smtlibParser.mly"
                                        ( Z.of_string _1 )
# 669 "smtlib/smtlibParser.ml"
               : 'numeral))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 193 "smtlib/smtlibParser.mly"
                                        ( _1 )
# 676 "smtlib/smtlibParser.ml"
               : 'decimal))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 197 "smtlib/smtlibParser.mly"
                                        ( String.uppercase_ascii _1 )
# 683 "smtlib/smtlibParser.ml"
               : 'hexadecimal))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 201 "smtlib/smtlibParser.mly"
                                        ( _1 )
# 690 "smtlib/smtlibParser.ml"
               : 'binary))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 205 "smtlib/smtlibParser.mly"
                                        ( _1 )
# 697 "smtlib/smtlibParser.ml"
               : 'string))
; (fun __caml_parser_env ->
    Obj.repr(
# 209 "smtlib/smtlibParser.mly"
                                        ( true )
# 703 "smtlib/smtlibParser.ml"
               : 'bool_value))
; (fun __caml_parser_env ->
    Obj.repr(
# 210 "smtlib/smtlibParser.mly"
                                        ( false )
# 709 "smtlib/smtlibParser.ml"
               : 'bool_value))
(* Entry file *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let file (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Ast.file)
