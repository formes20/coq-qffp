
open Extraction.ExtrOcamlIntConv
open Extraction.Datatypes
open Extraction.BinNums
open Extraction
open Extraction.QFBV
open Extraction.EqVar
open Extraction.Typ
open Extraction.TypEnv
open Extraction.NBitsDef
open Extraction.Seqs
open Extraction.QFBVHash
open Extraction.BitBlastingInit
open Extraction.BitBlastingCacheHash
open Extraction.State
open Util
open Smtlib.Ast

open Extraction.Fq2bvq
open Extraction.WBCommon
open Extraction.WBRounding
open Extraction.WBMain




(** Options and exceptions *)

let option_certify_sat = ref true
let option_certify_unsat = ref true

let option_kissat_path = ref "kissat"

let option_gratgen_path = ref "gratgen"

let option_gratchk_path = ref "gratchk"

let option_debug = ref false

let option_split_conjs = ref false

let option_expand_let = ref false

let option_verbose = ref false

let option_keep_temp_files = ref false

let option_cnf_file = ref None
let option_drat_file = ref None
let option_sat_log_file = ref None
let option_gratl_file = ref None
let option_gratp_file = ref None
let option_grat_log_file = ref None

let option_tmpdir = ref None

let tmpfile prefix suffix =
  match !option_tmpdir with
  | None -> Filename.temp_file prefix suffix
  | Some dir -> Filename.temp_file ~temp_dir:dir prefix suffix

let unlink' file = if Sys.file_exists file then Unix.unlink file

let cleanup files = if not !option_keep_temp_files then List.iter unlink' files


exception IllFormedException



(** Basic numbers conversion *)

let string_of_bits bs =
  String.concat "" (List.map (fun b -> if b then "1" else "0") (List.rev bs))

let explode s = List.init (String.length s) (String.get s)

let bits_of_z (size : int) (z : Z.t) : bits =
  let binstr =
    if z >= Z.zero then
      Z.format ("%0" ^ (string_of_int size) ^ "b") z
    else
      Z.format ("%0" ^ (string_of_int size) ^ "b")
        (Z.add (Z.pow (Z.of_int 2) size) z) in
  let rec helper i max str res =
    if i >= max then res
    else match String.get str i with
    | '0' -> helper (succ i) max str (false::res)
    | '1' -> helper (succ i) max str (true::res)
    | _ -> assert false in
  helper 0 (String.length binstr) binstr []

let pos_of_z z =
  let str = Z.format "b" z in
  let str = String.sub str 1 (String.length str - 1) in
  List.fold_left (
  fun p c ->
	if c = '1' then Coq_xI p
	else Coq_xO p) Coq_xH (explode str)

let rec z_of_pos n =
  match n with
  | Coq_xH -> Z.succ Z.zero
  | Coq_xO p -> Z.shift_left (z_of_pos p) 1
  | Coq_xI p -> Z.succ (Z.shift_left (z_of_pos p) 1)

let coq_z_of_z z =
  if Z.equal z Z.zero then Z0
  else if Z.lt z Z.zero then Zneg (pos_of_z (Z.neg z))
  else Zpos (pos_of_z z)

let z_of_coq_z n =
  match n with
  | Z0 -> Z.zero
  | Zpos p -> z_of_pos p
  | Zneg p -> Z.neg (z_of_pos p)



(** QFBV string outputs *)

let string_of_ty ty =
  match ty with
  | Tuint n
  | Tsint n -> string_of_int n

let string_of_eunop (op : QFBV.eunop) =
  match op with
  | QFBV.Unot -> "!"
  | QFBV.Uneg -> "-"
  | QFBV.Uextr (i, j) -> "extr " ^ string_of_int i ^ " " ^ string_of_int j
  | QFBV.Uhigh n -> "high " ^ string_of_int n
  | QFBV.Ulow n -> "low " ^ string_of_int n
  | QFBV.Uzext n -> "zext " ^ string_of_int n
  | QFBV.Usext n -> "sext " ^ string_of_int n
  | QFBV.Urepeat n -> "repeat " ^ string_of_int n
  | QFBV.Urotl n -> "rotate_left " ^ string_of_int n
  | QFBV.Urotr n -> "rotate_right " ^ string_of_int n

let string_of_ebinop (op : QFBV.ebinop) =
  match op with
  | QFBV.Band -> "&"
  | QFBV.Bor -> "|"
  | QFBV.Bxor -> "^"
  | QFBV.Badd -> "+"
  | QFBV.Bsub -> "-"
  | QFBV.Bmul -> "*"
  | QFBV.Bdiv -> "div"
  | QFBV.Bmod -> "mod"
  | QFBV.Bsdiv -> "sdiv"
  | QFBV.Bsrem -> "srem"
  | QFBV.Bsmod -> "smod"
  | QFBV.Bshl -> ">>"
  | QFBV.Blshr -> "<<l"
  | QFBV.Bashr -> "<<a"
  | QFBV.Bconcat -> "++"
  | QFBV.Bcomp -> "comp"

let string_of_bbinop (op : QFBV.bbinop) =
  match op with
  | QFBV.Beq -> "="
  | QFBV.Bult -> "<"
  | QFBV.Bule -> "<="
  | QFBV.Bugt -> ">"
  | QFBV.Buge -> ">="
  | QFBV.Bslt -> "<s"
  | QFBV.Bsle -> "<=s"
  | QFBV.Bsgt -> ">s"
  | QFBV.Bsge -> ">=s"
  | QFBV.Buaddo -> "uaddo"
  | QFBV.Busubo -> "usubo"
  | QFBV.Bumulo -> "umulo"
  | QFBV.Bsaddo -> "saddo"
  | QFBV.Bssubo -> "ssubo"
  | QFBV.Bsmulo -> "smulo"

let rec string_of_exp (e : QFBV.exp) : string =
  match e with
  | QFBV.Evar v -> let (vn, vi) = Obj.magic v in
                   "(" ^ string_of_int (int_of_n vn) ^ ", " ^ string_of_int (int_of_n vi) ^ ")"
  | QFBV.Econst n -> string_of_bits n
  | QFBV.Eunop (op, e) -> string_of_eunop op ^ " (" ^ string_of_exp e ^ ")"
  | QFBV.Ebinop (op, e1, e2) -> "(" ^ string_of_exp e1 ^ ") " ^ string_of_ebinop op ^ " (" ^ string_of_exp e2 ^ ")"
  | QFBV.Eite (c, e1, e2) -> "(" ^ string_of_bexp c ^ "  " ^ string_of_exp e1 ^ " : " ^ string_of_exp e2 ^ ")"
and string_of_bexp (e : QFBV.bexp) : string =
  match e with
  | QFBV.Bfalse -> "false"
  | QFBV.Btrue -> "true"
  | QFBV.Bbinop (op, e1, e2) -> "(" ^ string_of_exp e1 ^ ") " ^ string_of_bbinop op ^ " (" ^ string_of_exp e2 ^ ")"
  | QFBV.Blneg e -> "~ (" ^ string_of_bexp e ^ ")"
  | QFBV.Bconj (e1, e2) -> "(" ^ string_of_bexp e1 ^ ") /\\ (" ^ string_of_bexp e2 ^ ")"
  | QFBV.Bdisj (e1, e2) -> "(" ^ string_of_bexp e1 ^ ") \\/ (" ^ string_of_bexp e2 ^ ")"


(** QFBV helper functions *)

let make_qfbv_bvadds es =
  let rec helper res es =
    match es with
    | [] -> res
    | e::tl -> helper (QFBV.Ebinop (QFBV.Badd, res, e)) tl in
  match es with
  | [] -> failwith ("Apply bvadd with 0 argument")
  | e::tl -> helper e tl

let make_qfbv_conjs es =
  let rec helper res es =
    match es with
    | [] -> res
    | e::tl -> helper (QFBV.Bconj (res, e)) tl in
  match es with
  | [] -> QFBV.Bfalse
  | e::tl -> helper e tl

let make_qfbv_disjs es =
  let rec helper res es =
    match es with
    | [] -> res
    | e::tl -> helper (QFBV.Bdisj (res, e)) tl in
  match es with
  | [] -> QFBV.Btrue
  | e::tl -> helper e tl

let make_qfbv_imp e1 e2 = QFBV.Bdisj (QFBV.Blneg e1, e2)

let make_qfbv_iff e1 e2 = QFBV.Bconj (make_qfbv_imp e1 e2, make_qfbv_imp e2 e1)

let make_qfbv_diff e1 e2 = QFBV.Bdisj (QFBV.Bconj (e1, QFBV.Blneg e2), QFBV.Bconj (QFBV.Blneg e1, e2))

(** Fq2bvq helper functions *)
let make_fq2bvq_conjs es =
  let rec helper res es =
    match es with
    | [] -> res
    | e::tl -> helper (Fq2bvq.FBconj (res, e)) tl in
  match es with
  | [] -> Fq2bvq.FBfalse
  | e::tl -> helper e tl

let make_fq2bvq_disjs es =
  let rec helper res es =
    match es with
    | [] -> res
    | e::tl -> helper (Fq2bvq.FBdisj (res, e)) tl in
  match es with
  | [] -> Fq2bvq.FBtrue
  | e::tl -> helper e tl

let make_fq2bvq_imp e1 e2 = Fq2bvq.FBdisj (Fq2bvq.FBlneg e1, e2)

let make_fq2bvq_iff e1 e2 = Fq2bvq.FBconj (make_fq2bvq_imp e1 e2, make_fq2bvq_imp e2 e1)

let make_fq2bvq_diff e1 e2 = Fq2bvq.FBdisj (Fq2bvq.FBconj (e1, Fq2bvq.FBlneg e2), Fq2bvq.FBconj (Fq2bvq.FBlneg e1, e2))

let coq_typ_of_ttyp t : typ =
  match t with
  | TBool -> Tuint 1
  | TNumeral -> failwith ("Conversion from TNumeral to Coq Typ.t is not allowed")
  | TBitVec n -> Tuint n
  | TFloatVec (eb, sb) -> Tuint (eb+sb)
  | TRoundingMode -> Tuint 3


(** Conversion from SMT file to QFBV expressions *)

(* A map from a variable symbol to its ssavar *)
type vm = ssavar M.t

let gen_ssavar (svar : int) : ssavar * int =
  (Obj.repr (n_of_int svar, n_of_int 0), svar + 1)

(*
let get_sort_type (s : sort) : typ =
  match s with
  | SIdentifier (ISimple s) when s = "Bool" -> Tuint 1
  | SIdentifier (IIndexed (s, [INumeral n])) when s = "BitVec" -> Tuint (Z.to_int n)
  | _ -> failwith ("Unsupported sort: " ^ string_of_sort s)
 *)

type exp =
  | Ebv of QFBV.exp
  | Efp of Fq2bvq.fp_exp

let match_Ebv e : QFBV.exp =
  match e with 
  | Ebv ebv -> ebv
  | Efp efp -> failwith ("Arguments matching bv error")

let match_Efp e : Fq2bvq.fp_exp =
  match e with
  | Ebv ebv -> failwith ("Arguments matching fp error")
  | Efp efp -> efp

let convert_exp_spec_constant sc : exp =
  match sc with
  | CNumeral n -> failwith ("Conversion from numeral to QFBV exp is not supported.")
  | CDecimal _ -> failwith ("Conversion from decimal to QFBV exp is not supported.")
  | CHexDecimal h ->
     (try
        Ebv (QFBV.Econst (bits_of_z (String.length h * 4) (Z.of_string ("0x" ^ h))))
      with Invalid_argument _ ->
        failwith ("Failed to convert hex decimal: " ^ h))
  | CBinary b ->
     (try
        Ebv (QFBV.Econst (bits_of_z (String.length b) (Z.of_string ("0b" ^ b))))
      with Invalid_argument _ ->
        failwith ("Failed to convert binary: " ^ b))
  | CString _ -> failwith ("Conversion from string to QFBV exp is not supported.")

let convert_fp_bexp_spec_constant sc : Fq2bvq.fp_bexp =
  failwith ("Conversion from spec_constant to Fq2bvq fp_bexp is not supported")

let convert_exp_identifier vm tm i : exp =
  match i with
  | ISimple v ->
      if v = "RNE" || v = "roundNearestTiesToEven" then Ebv rne_exp
      else if v = "RNA" || v = "roundNearestTiesToAway" then Ebv rna_exp
      else if v = "RTP" || v = "roundTowardPositive" then Ebv rtp_exp
      else if v = "RTN" || v = "roundTowardNegative" then Ebv rtn_exp
      else if v = "RTZ" || v = "roundTowardZero" then Ebv rtz_exp
      else  (
              try
                let ty = ttyp_of_identifier tm i in
                begin
                  match ty with
                  | TRoundingMode -> Ebv (QFBV.Evar (M.find v vm))
                  | TBitVec n -> Ebv (QFBV.Evar (M.find v vm))
                  | TFloatVec (eb, sb) -> let s = QFBV.Evar (M.find (v ^ "_s") vm) in
                                          let e = QFBV.Evar (M.find (v ^ "_e") vm) in
                                          let m = QFBV.Evar (M.find (v ^ "_m") vm) in
                                            Efp (Fq2bvq.FEieee754 (eb, (sb-1), s, e, m))
                  | TBool -> failwith ("Boolean variable " ^ v ^ " does not support conversion to exp.")
                  | TNumeral -> failwith ("Numeral variable " ^ v ^ " is not supported.")
                  end
              with Not_found ->
                failwith("Variable " ^ v ^ " is not declared.")
            )
  | IIndexed (v, [INumeral n]) ->
     if Str.string_match (Str.regexp "bv\\([0-9]+\\)") v 0
     then Ebv (QFBV.Econst (bits_of_z (Z.to_int n) (Z.of_string (Str.matched_group 1 v))))
     else failwith ("Unrecognized identifier " ^ string_of_identifier i)
  | IIndexed (v, (INumeral eb)::(INumeral sb)::[]) ->
     let eb = Z.to_int eb in
     let sb = Z.to_int sb in
     if Str.string_match (Str.regexp "+zero") v 0
      then Efp (Fq2bvq.FEieee754 (eb, (sb-1), coq_Bfalse_exp, zero_exp eb, zero_exp (sb-1)))
     else if Str.string_match (Str.regexp "-zero") v 0
      then Efp (Fq2bvq.FEieee754 (eb, (sb-1), coq_Btrue_exp, zero_exp eb, zero_exp (sb-1)))
     else if Str.string_match (Str.regexp "+oo") v 0
      then Efp (Fq2bvq.FEieee754 (eb, (sb-1), coq_Bfalse_exp, ones_exp eb, zero_exp (sb-1)))
     else if Str.string_match (Str.regexp "-oo") v 0
      then Efp (Fq2bvq.FEieee754 (eb, (sb-1), coq_Btrue_exp, ones_exp eb, zero_exp (sb-1)))
     else if Str.string_match (Str.regexp "NaN") v 0
      then Efp (Fq2bvq.FEieee754 (eb, (sb-1), coq_Btrue_exp, ones_exp eb, ones_exp (sb-1)))
     else failwith ("Unrecognized identifier " ^ string_of_identifier i)
  | _ -> failwith ("Unrecognized identifier " ^ string_of_identifier i)

let convert_fp_bexp_identifier vm tm i : Fq2bvq.fp_bexp =
  match i with
  | ISimple v -> if v = "true" then Fq2bvq.FBtrue
                 else if v = "false" then Fq2bvq.FBfalse
                 else (try
                        Fq2bvq.FBvar (QFBV.Evar (M.find v vm))
                       with Not_found ->
                         failwith("Variable " ^ v ^ " is not declared.")
                      )
  | IIndexed (v, is) -> failwith ("Conversion from indexed variables to Fq2bvq boolean expressions is not supported.")

let convert_exp_qual_identifier vm tm qi : exp =
  match qi with
  | QIdentifier i -> convert_exp_identifier vm tm i
  | QAnnotated (i, s) -> convert_exp_identifier vm tm i

let convert_fp_bexp_qual_identifier vm tm qi : Fq2bvq.fp_bexp =
  match qi with
  | QIdentifier i -> convert_fp_bexp_identifier vm tm i
  | QAnnotated (i, s) -> convert_fp_bexp_identifier vm tm i

let rec convert_exp_application es vm tm fm sm env g fqi factuals : SSATE.env * int * Fq2bvq.fp_bexp list * exp =
  let fn = symbol_of_qual_identifier fqi in
  match fqi, factuals with
  (* Core *)
  | QIdentifier (ISimple v), a1::a2::a3::[] when v = fn_ite -> let (env1, g1, es1, be) = convert_fp_bexp_term es vm tm fm sm env g a1 in
                                                               let (env2, g2, es2, e1) = convert_exp_term es1 vm tm fm sm env1 g1 a2 in
                                                               let (env3, g3, es3, e2) = convert_exp_term es2 vm tm fm sm env2 g2 a3 in
                                                               let fe1 = match_Efp e1 in
                                                               let fe2 = match_Efp e2 in
                                                               (env3, g3, es3, Efp (Fq2bvq.FEite (be, fe1, fe2)))
  (* Floating-point operations *)
  | QIdentifier (ISimple v), a1::[] when v = fn_fp_abs -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm sm env g a1 in
                                                          let fe1 = match_Efp e1 in
                                                            (env1, g1, es1, Efp (Fq2bvq.FEunop (Fq2bvq.FUabs, fe1)))              
  | QIdentifier (ISimple v), a1::[] when v = fn_fp_neg -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm sm env g a1 in
                                                          let fe1 = match_Efp e1 in
                                                            (env1, g1, es1, Efp (Fq2bvq.FEunop (Fq2bvq.FUneg, fe1)))       
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_fp_max -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm sm env g a1 in
                                                              let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm sm env1 g1 a2 in
                                                              let fe1 = match_Efp e1 in
                                                              let fe2 = match_Efp e2 in
                                                                (env2, g2, es2, Efp (Fq2bvq.FEbinop (Fq2bvq.FBmax, fe1, fe2)))   
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_fp_min -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm sm env g a1 in
                                                              let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm sm env1 g1 a2 in
                                                              let fe1 = match_Efp e1 in
                                                              let fe2 = match_Efp e2 in
                                                                (env2, g2, es2, Efp (Fq2bvq.FEbinop (Fq2bvq.FBmin, fe1, fe2)))  
  | QIdentifier (ISimple v), a1::a2::a3::[] when v = fn_fp_mul -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm sm env g a1 in
                                                                  let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm sm env1 g1 a2 in
                                                                  let (env3, g3, es3, e3) = convert_exp_term es2 vm tm fm sm env2 g2 a3 in
                                                                  let rm = match_Ebv e1 in
                                                                  let fe1 = match_Efp e2 in
                                                                  let fe2 = match_Efp e3 in
                                                                    (env3, g3, es3, Efp (Fq2bvq.FErmbinop (Fq2bvq.FRBmul, rm, fe1, fe2)))
  | QIdentifier (ISimple v), a1::a2::a3::[] when v = fn_fp_add -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm sm env g a1 in
                                                                  let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm sm env1 g1 a2 in
                                                                  let (env3, g3, es3, e3) = convert_exp_term es2 vm tm fm sm env2 g2 a3 in
                                                                  let rm = match_Ebv e1 in
                                                                  let fe1 = match_Efp e2 in
                                                                  let fe2 = match_Efp e3 in
                                                                    (env3, g3, es3, Efp (Fq2bvq.FErmbinop (Fq2bvq.FRBadd, rm, fe1, fe2)))
  | QIdentifier (ISimple v), a1::a2::a3::[] when v = fn_fp_sub -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm sm env g a1 in
                                                                  let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm sm env1 g1 a2 in
                                                                  let (env3, g3, es3, e3) = convert_exp_term es2 vm tm fm sm env2 g2 a3 in
                                                                  let rm = match_Ebv e1 in
                                                                  let fe1 = match_Efp e2 in
                                                                  let fe2 = match_Efp e3 in
                                                                    (env3, g3, es3, Efp (Fq2bvq.FErmbinop (Fq2bvq.FRBsub, rm, fe1, fe2)))
  | QIdentifier (ISimple v), a1::a2::a3::a4::[] when v = fn_fp_fma -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm sm env g a1 in
                                                                      let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm sm env1 g1 a2 in
                                                                      let (env3, g3, es3, e3) = convert_exp_term es2 vm tm fm sm env2 g2 a3 in
                                                                      let (env4, g4, es4, e4) = convert_exp_term es3 vm tm fm sm env3 g3 a4 in
                                                                      let rm = match_Ebv e1 in
                                                                      let fe1 = match_Efp e2 in
                                                                      let fe2 = match_Efp e3 in
                                                                      let fe3 = match_Efp e4 in
                                                                        (env4, g4, es4, Efp (Fq2bvq.FErmtriop (Fq2bvq.FRTfma, rm, fe1, fe2, fe3))) 
  | QIdentifier (ISimple v), a1::a2::a3::[] when v = fn_fp_div -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm sm env g a1 in
                                                                  let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm sm env1 g1 a2 in
                                                                  let (env3, g3, es3, e3) = convert_exp_term es2 vm tm fm sm env2 g2 a3 in
                                                                  let rm = match_Ebv e1 in
                                                                  let fe1 = match_Efp e2 in
                                                                  let fe2 = match_Efp e3 in
                                                                    (env3, g3, es3, Efp (Fq2bvq.FErmbinop (Fq2bvq.FRBdiv, rm, fe1, fe2)))   
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_fp_sqrt ->  let (env1, g1, es1, e1) = convert_exp_term es vm tm fm sm env g a1 in
                                                                let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm sm env1 g1 a2 in
                                                                let rm = match_Ebv e1 in
                                                                let fe = match_Efp e2 in
                                                                  (env2, g2, es2, Efp (Fq2bvq.FErmunop (Fq2bvq.FRUsqrt, rm, fe)))
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_fp_rem ->   let (env1, g1, es1, e1) = convert_exp_term es vm tm fm sm env g a1 in
                                                                let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm sm env1 g1 a2 in
                                                                let fe1 = match_Efp e1 in
                                                                let fe2 = match_Efp e2 in
                                                                  (env2, g2, es2, Efp (Fq2bvq.FEbinop (Fq2bvq.FBrem, fe1, fe2))) 
 | QIdentifier (ISimple v), a1::a2::[] when v = fn_fp_roundToIntegral ->  let (env1, g1, es1, e1) = convert_exp_term es vm tm fm sm env g a1 in
                                                                          let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm sm env1 g1 a2 in
                                                                          let rm = match_Ebv e1 in
                                                                          let fe = match_Efp e2 in
                                                                            (env2, g2, es2, Efp (Fq2bvq.FErmunop (Fq2bvq.FRUrti, rm, fe)))
  | QIdentifier (IIndexed (v, (INumeral eb)::(INumeral sb)::[])), a1::[] when v = fn_to_fp -> let ty = ttyp_of_term tm fm sm a1 in
                                                                                              let eb = Z.to_int eb in
                                                                                              let sb = Z.to_int sb in
                                                                                              begin
                                                                                                match ty with
                                                                                                | TBitVec n ->  let (env1, g1, es1, e1) = convert_exp_term es vm tm fm sm env g a1 in
                                                                                                                let e = match_Ebv e1 in
                                                                                                                  (env1, g1, es1, Efp (Fq2bvq.FEofbv (e, n, eb, (sb-1))))
                                                                                                | _ -> raise IllFormedException
                                                                                              end
  | QIdentifier (IIndexed (v, (INumeral eb)::(INumeral sb)::[])), a1::a2::[] when v = fn_to_fp -> let ty = ttyp_of_term tm fm sm a2 in
                                                                                                  let eb = Z.to_int eb in
                                                                                                  let sb = Z.to_int sb in
                                                                                                  begin
                                                                                                    match ty with
                                                                                                    | TFloatVec (mb, nb) -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm sm env g a1 in
                                                                                                                            let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm sm env1 g1 a2 in
                                                                                                                            let rm = match_Ebv e1 in
                                                                                                                            let fe = match_Efp e2 in
                                                                                                                              (env2, g2, es2, Efp (Fq2bvq.FEofbf (rm, fe, eb, (sb-1))))
                                                                                                    | TBitVec n ->  let (env1, g1, es1, e1) = convert_exp_term es vm tm fm sm env g a1 in
                                                                                                                    let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm sm env1 g1 a2 in
                                                                                                                    let rm = match_Ebv e1 in
                                                                                                                    let e = match_Ebv e2 in
                                                                                                                      (env2, g2, es2, Efp (Fq2bvq.FEofsbv (rm, e, n, eb, (sb-1))))  
                                                                                                    | _ -> raise IllFormedException
                                                                                                  end
  | QIdentifier (IIndexed (v, (INumeral eb)::(INumeral sb)::[])), a1::a2::[] when v = fn_to_fp_unsigned ->  let ty = ttyp_of_term tm fm sm a2 in
                                                                                                            let eb = Z.to_int eb in
                                                                                                            let sb = Z.to_int sb in
                                                                                                            begin
                                                                                                              match ty with
                                                                                                              | TBitVec n ->  let (env1, g1, es1, e1) = convert_exp_term es vm tm fm sm env g a1 in
                                                                                                                              let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm sm env1 g1 a2 in
                                                                                                                              let rm = match_Ebv e1 in
                                                                                                                              let e = match_Ebv e2 in
                                                                                                                                (env2, g2, es2, Efp (Fq2bvq.FEofubv (rm, e, n, eb, (sb-1))))  
                                                                                                              | _ -> raise IllFormedException
                                                                                                            end
  | QIdentifier (ISimple v), a1::a2::a3::[] when v = "fp" ->
      let ty_s = ttyp_of_term tm fm sm a1 in
      let ty_e = ttyp_of_term tm fm sm a2 in
      let ty_m = ttyp_of_term tm fm sm a3 in
      begin
        match ty_s, ty_e, ty_m with
        | TBitVec s, TBitVec eb, TBitVec sb -> 
              let (env1, g1, es1, e1) = convert_exp_term es vm tm fm sm env g a1 in
              let (env2, g2, es2, e2) = convert_exp_term es vm tm fm sm env g1 a2 in
              let (env3, g3, es3, e3) = convert_exp_term es vm tm fm sm env g2 a3 in
              let s = match_Ebv e1 in
              let e = match_Ebv e2 in
              let m = match_Ebv e3 in
                (env3, g3, es3, Efp (Fq2bvq.FEieee754 (eb, sb, s, e, m)))                       
        | _, _, _ -> raise IllFormedException
      end
  (* User-defined functions *)
  | _ ->
    try
      let (fargs, fsort, fterm) = M.find fn fm in
      let fargs = fst (List.split fargs) in
      if List.length fargs <> List.length factuals then failwith ("Number of arguments mismatch in function application: " ^ fn)
      else convert_exp_term es vm tm fm sm env g (List.fold_left2 (fun t arg actual -> subst_term arg actual t) fterm fargs factuals)
    with Not_found ->
      failwith ("Undefined exp function in function application: " ^ string_of_term (TApplication (fqi, factuals)))

and convert_exp_let es vm tm fm sm env g vbs t : SSATE.env * int * Fq2bvq.fp_bexp list * exp =
  if !option_expand_let then
    begin
      let t' = List.fold_left (
                   fun t (v, p) -> subst_term v p t
                 ) t vbs in
      convert_exp_term es vm tm fm sm env g t'
    end
  else
    match vbs with
    | [] -> convert_exp_term es vm tm fm sm env g t
    | (v, vt)::vbs -> let ty = ttyp_of_term tm fm sm vt in
                      let tm' = M.add v ty tm in
                      match ty with
                      | TRoundingMode -> failwith ("Bit-vector(RoundingMode) term is not supported in let statement of variable " ^ v)
                      | TBitVec _ -> failwith ("Bit-vector term is not supported in let statement of variable " ^ v)
                      | TFloatVec (eb, sb) -> let tm1 = M.add (v ^ "_s") (TBitVec 1) tm' in
                                              let tm2 = M.add (v ^ "_e") (TBitVec eb) tm1 in
                                              let tm3 = M.add (v ^ "_m") (TBitVec (sb-1)) tm2 in
                                              let coq_ty_s = Tuint 1 in
                                              let coq_ty_e = Tuint eb in
                                              let coq_ty_m = Tuint (sb-1) in
                                              let (coq_v_s, g1) = gen_ssavar g in
                                              let (coq_v_e, g2) = gen_ssavar g1 in
                                              let (coq_v_m, g3) = gen_ssavar g2 in
                                              let vm1 = M.add (v ^ "_s") coq_v_s vm in
                                              let vm2 = M.add (v ^ "_e") coq_v_e vm1 in
                                              let vm3 = M.add (v ^ "_m") coq_v_m vm2 in
                                              let env1 =  SSATE.add coq_v_s coq_ty_s env in
                                              let env2 =  SSATE.add coq_v_e coq_ty_e env1 in
                                              let env3 =  SSATE.add coq_v_m coq_ty_m env2 in
                                              let (env4, g4, es', e) = convert_exp_term es vm3 tm3 fm sm env3 g vt in
                                              let fe1 = match_Efp e in
                                              let fe2 = Fq2bvq.FEieee754 (eb, (sb-1), QFBV.Evar coq_v_s, QFBV.Evar coq_v_e, QFBV.Evar coq_v_m) in
                                              let e' = Fq2bvq.FBbveq (fe1, fe2) in
                                                convert_exp_let (e'::es') vm3 tm3 fm sm env3 g3 vbs t
                      | _ ->  let coq_ty = coq_typ_of_ttyp ty in
                              let (coq_v, g') = gen_ssavar g in
                              let vm' = M.add v coq_v vm in
                              let env' = SSATE.add coq_v coq_ty env in
                              match ty with 
                              | TRoundingMode -> failwith ("Bit-vector(RoundingMode) term is not supported in let statement of variable " ^ v)
                              | TBitVec _ -> failwith ("Bit-vector term is not supported in let statement of variable " ^ v)
                              | _ -> let (env'', g'', es', e) = convert_fp_bexp_term es vm' tm' fm sm env' g' (make_eq (make_var v) vt) in
                                      convert_exp_let (e::es') vm' tm' fm sm env'' g'' vbs t  

and convert_exp_term es vm tm fm sm env g t : SSATE.env * int * Fq2bvq.fp_bexp list * exp =
  match t with
  | TConstant sc -> (env, g, es, convert_exp_spec_constant sc)
  | TVariable qi -> (env, g, es, convert_exp_qual_identifier vm tm qi)
  | TApplication (fqi, factuals) -> convert_exp_application es vm tm fm sm env g fqi factuals
  | TLet (vbs, t) -> convert_exp_let es vm tm fm sm env g vbs t

and convert_fp_bexp_application es vm tm fm sm env g fqi factuals : SSATE.env * int * Fq2bvq.fp_bexp list * Fq2bvq.fp_bexp =
  let fn = symbol_of_qual_identifier fqi in
  match fqi, factuals with
  (* Core *)
  | QIdentifier (ISimple v), a::[] when v = fn_not -> let (env1, g1, es1, e1) = convert_fp_bexp_term es vm tm fm sm env g a in
                                                      (env1, g1, es1, Fq2bvq.FBlneg e1)
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_imp -> let (env1, g1, es1, e1) = convert_fp_bexp_term es vm tm fm sm env g a1 in
                                                           let (env2, g2, es2, e2) = convert_fp_bexp_term es1 vm tm fm sm env1 g1 a2 in
                                                           (env2, g2, es2, make_fq2bvq_imp e1 e2)
  | QIdentifier (ISimple v), _ when v = fn_and -> let (env', g', es, es_a) = List.fold_left (
                                                                                 fun (env, g, es, es_a) a ->
                                                                                 let (env1, g1, es1, e1) = convert_fp_bexp_term es vm tm fm sm env g a in
                                                                                 (env1, g1, es1, e1::es_a)
                                                                               ) (env, g, es, []) factuals in
                                                  (env', g', es, make_fq2bvq_conjs (List.rev es_a))
  | QIdentifier (ISimple v), _ when v = fn_or -> let (env', g', es, es_a) = List.fold_left (
                                                                                fun (env, g, es, es_a) a ->
                                                                                let (env1, g1, es1, e1) = convert_fp_bexp_term es vm tm fm sm env g a in
                                                                                (env1, g1, es1, e1::es_a)
                                                                              ) (env, g, es, []) factuals in
                                                 (env', g', es, make_fq2bvq_disjs (List.rev es_a))
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_xor -> failwith ("xor is not supported")
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_eq -> if is_bool_term tm fm sm a1 || is_bool_term tm fm sm a2
                                                          then let (env1, g1, es1, e1) = convert_fp_bexp_term es vm tm fm sm env g a1 in
                                                               let (env2, g2, es2, e2) = convert_fp_bexp_term es1 vm tm fm sm env1 g1 a2 in
                                                               (env2, g2, es2, make_fq2bvq_iff e1 e2)
                                                          else let (env1, g1, es1, e1) = convert_exp_term es vm tm fm sm env g a1 in
                                                               let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm sm env1 g1 a2 in
                                                               let fe1 = match_Efp e1 in
                                                               let fe2 = match_Efp e2 in
                                                                 (env2, g2, es2, Fq2bvq.FBbveq (fe1, fe2))
  | QIdentifier (ISimple v), _ when v = fn_eq -> failwith (v ^ " currently does not support chainable")
  | QIdentifier (ISimple v), _ when v = fn_distinct ->  if List.exists (is_bool_term tm fm sm) factuals
                                                        then let (env', g', es, es_as) = List.fold_left (
                                                                                            fun (env, g, es, es_as) a ->
                                                                                            let (env1, g1, es1, e1) = convert_fp_bexp_term es vm tm fm sm env g a in
                                                                                            (env1, g, es1, e1::es_as)
                                                                                          ) (env, g, es, []) factuals in
                                                            (env', g', es, make_fq2bvq_conjs (List.map (fun es -> match es with
                                                                                                                | e1::e2::[] -> make_fq2bvq_diff e1 e2
                                                                                                                | _ -> failwith("Never happen")) (Util.combinations 2 es_as)))
                                                        else let (env', g', es, es_as) = List.fold_left (
                                                                                            fun (env, g, es, es_as) a ->
                                                                                            let (env1, g1, es1, e1) = convert_exp_term es vm tm fm sm env g a in
                                                                                            let fe1 = match_Efp e1 in
                                                                                            (env1, g, es1, fe1::es_as)
                                                                                          ) (env, g, es, []) factuals in
                                                            (env', g', es, make_fq2bvq_conjs (List.map (fun es -> match es with
                                                                                                                | e1::e2::[] -> Fq2bvq.FBlneg (Fq2bvq.FBbveq (e1, e2))
                                                                                                                | _ -> failwith("Never happen")) (Util.combinations 2 es_as)))
  | QIdentifier (ISimple v), a1::a2::a3::[] when v = fn_ite -> let (env1, g1, es1, e1) = convert_fp_bexp_term es vm tm fm sm env g a1 in
                                                               let (env2, g2, es2, e2) = convert_fp_bexp_term es1 vm tm fm sm env1 g1 a2 in
                                                               let (env3, g3, es3, e3) = convert_fp_bexp_term es2 vm tm fm sm env2 g2 a3 in
                                                               (env3, g3, es3, Fq2bvq.FBdisj (Fq2bvq.FBconj (e1, e2), Fq2bvq.FBconj (Fq2bvq.FBlneg e1, e3)))
  (* floating-point operations *)
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_fp_eq ->  let (env1, g1, es1, e1) = convert_exp_term es vm tm fm sm env g a1 in
                                                              let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm sm env1 g1 a2 in
                                                              let fe1 = match_Efp e1 in
                                                              let fe2 = match_Efp e2 in
                                                              (env2, g2, es2, Fq2bvq.FBbinop (Fq2bvq.FBeq, fe1, fe2))
  | QIdentifier (ISimple v), a1::[] when v = fn_fp_isZero ->  let (env1, g1, es1, e1) = convert_exp_term es vm tm fm sm env g a1 in
                                                              let fe = match_Efp e1 in
                                                                  (env1, g1, es1, Fq2bvq.FBunop (Fq2bvq.FUisZero, fe))
  | QIdentifier (ISimple v), a1::[] when v = fn_fp_isNormal ->  let (env1, g1, es1, e1) = convert_exp_term es vm tm fm sm env g a1 in
                                                                let fe = match_Efp e1 in
                                                                  (env1, g1, es1, Fq2bvq.FBunop (Fq2bvq.FUisNormal, fe))
  | QIdentifier (ISimple v), a1::[] when v = fn_fp_isSubNormal -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm sm env g a1 in
                                                                  let fe = match_Efp e1 in
                                                                  (env1, g1, es1, Fq2bvq.FBunop (Fq2bvq.FUisSubnormal, fe))
  | QIdentifier (ISimple v), a1::[] when v = fn_fp_isInfinite ->  let (env1, g1, es1, e1) = convert_exp_term es vm tm fm sm env g a1 in
                                                                  let fe = match_Efp e1 in           
                                                                   (env1, g1, es1, Fq2bvq.FBunop (Fq2bvq.FUisInfinite, fe))
  | QIdentifier (ISimple v), a1::[] when v = fn_fp_isNaN ->  let (env1, g1, es1, e1) = convert_exp_term es vm tm fm sm env g a1 in
                                                             let fe = match_Efp e1 in
                                                               (env1, g1, es1, Fq2bvq.FBunop (Fq2bvq.FUisNaN, fe))
  | QIdentifier (ISimple v), a1::[] when v = fn_fp_isPositive ->  let (env1, g1, es1, e1) = convert_exp_term es vm tm fm sm env g a1 in
                                                                  let fe = match_Efp e1 in
                                                                    (env1, g1, es1, Fq2bvq.FBunop (Fq2bvq.FUisPositive, fe))
  | QIdentifier (ISimple v), a1::[] when v = fn_fp_isNegative ->  let (env1, g1, es1, e1) = convert_exp_term es vm tm fm sm env g a1 in
                                                                  let fe = match_Efp e1 in
                                                                   (env1, g1, es1, Fq2bvq.FBunop (Fq2bvq.FUisNegative, fe))
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_fp_lt ->  let (env1, g1, es1, e1) = convert_exp_term es vm tm fm sm env g a1 in
                                                              let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm sm env1 g1 a2 in
                                                              let fe1 = match_Efp e1 in
                                                              let fe2 = match_Efp e2 in
                                                                  (env2, g2, es2, Fq2bvq.FBbinop (Fq2bvq.FBlt, fe1, fe2))
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_fp_gt ->  let (env1, g1, es1, e1) = convert_exp_term es vm tm fm sm env g a1 in
                                                              let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm sm env1 g1 a2 in
                                                              let fe1 = match_Efp e1 in
                                                              let fe2 = match_Efp e2 in
                                                                  (env2, g2, es2, Fq2bvq.FBbinop (Fq2bvq.FBgt, fe1, fe2))
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_fp_leq -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm sm env g a1 in
                                                              let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm sm env1 g1 a2 in
                                                              let fe1 = match_Efp e1 in
                                                              let fe2 = match_Efp e2 in
                                                                  (env2, g2, es2, Fq2bvq.FBbinop (Fq2bvq.FBleq, fe1, fe2))
  | QIdentifier (ISimple v), a1::a2::[] when v = fn_fp_geq -> let (env1, g1, es1, e1) = convert_exp_term es vm tm fm sm env g a1 in
                                                              let (env2, g2, es2, e2) = convert_exp_term es1 vm tm fm sm env1 g1 a2 in
                                                              let fe1 = match_Efp e1 in
                                                              let fe2 = match_Efp e2 in
                                                                  (env2, g2, es2, Fq2bvq.FBbinop (Fq2bvq.FBgeq, fe1, fe2))
  | QIdentifier (ISimple v), _ when v = fn_fp_eq -> failwith (v ^ " currently does not support chainable")
  | QIdentifier (ISimple v), _ when v = fn_fp_lt -> failwith (v ^ " currently does not support chainable")
  | QIdentifier (ISimple v), _ when v = fn_fp_leq -> failwith (v ^ " currently does not support chainable")
  | QIdentifier (ISimple v), _ when v = fn_fp_gt -> failwith (v ^ " currently does not support chainable")
  | QIdentifier (ISimple v), _ when v = fn_fp_geq -> failwith (v ^ " currently does not support chainable")
  (* User-defined functions *)
  | _ ->
    try
      let (fargs, fsort, fterm) = M.find fn fm in
      let fargs = fst (List.split fargs) in
      if List.length fargs <> List.length factuals then failwith ("Number of arguments mismatch in function application: " ^ fn)
      else convert_fp_bexp_term es vm tm fm sm env g (List.fold_left2 (fun t arg actual -> subst_term arg actual t) fterm fargs factuals)
    with Not_found ->
      failwith ("Undefined fp_bexp function in function application: " ^ fn)

and convert_fp_bexp_let es vm tm fm sm env g vbs t : SSATE.env * int * Fq2bvq.fp_bexp list * Fq2bvq.fp_bexp =
  if !option_expand_let then
    begin
      let t' = List.fold_left (
                   fun t (v, p) -> subst_term v p t
                 ) t vbs in
      convert_fp_bexp_term es vm tm fm sm env g t'
    end
  else
    match vbs with
    | [] -> convert_fp_bexp_term es vm tm fm sm env g t
    | (v, vt)::vbs -> let ty = ttyp_of_term tm fm sm vt in
                      let tm' = M.add v ty tm in
                      match ty with
                      | TRoundingMode -> failwith ("Bit-vector(RoundingMode) term is not supported in let statement of variable " ^ v)
                      | TBitVec _ -> failwith ("Bit-vector term is not supported in let statement of variable " ^ v)
                      | TFloatVec (eb, sb) -> let tm1 = M.add (v ^ "_s") (TBitVec 1) tm' in
                                              let tm2 = M.add (v ^ "_e") (TBitVec eb) tm1 in
                                              let tm3 = M.add (v ^ "_m") (TBitVec (sb-1)) tm2 in
                                              let coq_ty_s = Tuint 1 in
                                              let coq_ty_e = Tuint eb in
                                              let coq_ty_m = Tuint (sb-1) in
                                              let (coq_v_s, g1) = gen_ssavar g in
                                              let (coq_v_e, g2) = gen_ssavar g1 in
                                              let (coq_v_m, g3) = gen_ssavar g2 in
                                              let vm1 = M.add (v ^ "_s") coq_v_s vm in
                                              let vm2 = M.add (v ^ "_e") coq_v_e vm1 in
                                              let vm3 = M.add (v ^ "_m") coq_v_m vm2 in
                                              let env1 =  SSATE.add coq_v_s coq_ty_s env in
                                              let env2 =  SSATE.add coq_v_e coq_ty_e env1 in
                                              let env3 =  SSATE.add coq_v_m coq_ty_m env2 in
                                              let (env4, g4, es', e) = convert_exp_term es vm3 tm3 fm sm env3 g vt in
                                              let fe1 = match_Efp e in
                                              let fe2 = Fq2bvq.FEieee754 (eb, (sb-1), QFBV.Evar coq_v_s, QFBV.Evar coq_v_e, QFBV.Evar coq_v_m) in
                                              let e' = Fq2bvq.FBbveq (fe1, fe2) in
                                                convert_fp_bexp_let (e'::es') vm3 tm3 fm sm env3 g3 vbs t
                      | _ ->  let coq_ty = coq_typ_of_ttyp ty in
                              let (coq_v, g') = gen_ssavar g in
                              let vm' = M.add v coq_v vm in
                              let env' = SSATE.add coq_v coq_ty env in
                              match ty with 
                              | TRoundingMode -> failwith ("Bit-vector(RoundingMode) term is not supported in let statement of variable " ^ v)
                              | TBitVec _ -> failwith ("Bit-vector term is not supported in let statement of variable " ^ v)
                              | _ -> let (env'', g'', es', e) = convert_fp_bexp_term es vm' tm' fm sm env' g' (make_eq (make_var v) vt) in
                                      convert_fp_bexp_let (e::es') vm' tm' fm sm env'' g'' vbs t

and convert_fp_bexp_term es vm tm fm sm env g t : SSATE.env * int * Fq2bvq.fp_bexp list * Fq2bvq.fp_bexp =
  match t with
  | TConstant sc -> (env, g, es, convert_fp_bexp_spec_constant sc)
  | TVariable qi -> (env, g, es, convert_fp_bexp_qual_identifier vm tm qi)
  | TApplication (fqi, factuals) -> convert_fp_bexp_application es vm tm fm sm env g fqi factuals
  | TLet (vbs, t) -> convert_fp_bexp_let es vm tm fm sm env g vbs t

let define_sort sm sn sargs ssort : sm =
  if sn = "RNE" || sn = "roundNearestTiesToEven" ||
    sn = "RNA" || sn = "roundNearestTiesToAway" ||
    sn = "RTP" || sn = "roundTowardPositive" ||
    sn = "RTN" || sn = "roundTowardNegative" ||
    sn = "RTZ" || sn = "roundTowardZero"
  then failwith (sn ^ " is a built-in identifier (of RoundingModes)")
  else match sargs with
  | [] -> M.add sn ssort sm
  | _ -> failwith ("Sort definition with nonempty arguments is not supported.")

let declare_fun vm tm fm sm env g fn fargs fsort : vm * tm * fm * SSATE.env * int =
  if fn = "RNE" || fn = "roundNearestTiesToEven" ||
    fn = "RNA" || fn = "roundNearestTiesToAway" ||
    fn = "RTP" || fn = "roundTowardPositive" ||
    fn = "RTN" || fn = "roundTowardNegative" ||
    fn = "RTZ" || fn = "roundTowardZero"
  then failwith(fn ^ " is a built-in identifier (of RoundingModes) ")
  else match fargs with
  | [] -> let ty = ttyp_of_sort fsort sm in
          begin
          match ty with
          | TFloatVec (eb, sb) ->  let tm1 = M.add (fn ^ "_s") (TBitVec 1) tm in
                                  let tm2 = M.add (fn ^ "_e") (TBitVec eb) tm1 in
                                  let tm3 = M.add (fn ^ "_m") (TBitVec (sb-1)) tm2 in
                                  let coq_ty_s = Tuint 1 in
                                  let coq_ty_e = Tuint eb in
                                  let coq_ty_m = Tuint (sb-1) in
                                  let (coq_v_s, g1) = gen_ssavar g in
                                  let (coq_v_e, g2) = gen_ssavar g1 in
                                  let (coq_v_m, g3) = gen_ssavar g2 in
                                  let vm1 = M.add (fn ^ "_s") coq_v_s vm in
                                  let vm2 = M.add (fn ^ "_e") coq_v_e vm1 in
                                  let vm3 = M.add (fn ^ "_m") coq_v_m vm2 in
                                  let env1 =  SSATE.add coq_v_s coq_ty_s env in
                                  let env2 =  SSATE.add coq_v_e coq_ty_e env1 in
                                  let env3 =  SSATE.add coq_v_m coq_ty_m env2 in
                                    (vm3, M.add fn ty tm3, fm, env3, g3)
          | _ ->  let coq_ty = coq_typ_of_ttyp ty in
                  let (coq_v, g') = gen_ssavar g in
                    (M.add fn coq_v vm, M.add fn ty tm, fm, SSATE.add coq_v coq_ty env, g')
          end
  | _ -> failwith ("Function declaration with nonempty arguments is not supported.")

let define_fun bves es vm tm fm sm env g fn fargs fsort fterm : vm * tm * fm * SSATE.env * int * Fq2bvq.fp_bexp list * QFBV.bexp list =
  if fn = "RNE" || fn = "roundNearestTiesToEven" ||
    fn = "RNA" || fn = "roundNearestTiesToAway" ||
    fn = "RTP" || fn = "roundTowardPositive" ||
    fn = "RTN" || fn = "roundTowardNegative" ||
    fn = "RTZ" || fn = "roundTowardZero"
  then failwith(fn ^ " is a built-in identifier (of RoundingModes) ")
  else match fargs with
  | [] -> let ty = ttyp_of_sort fsort sm in
          let tm' = M.add fn ty tm in
          begin
          match ty with
          | TRoundingMode ->  let coq_ty = coq_typ_of_ttyp ty in
                              let (coq_v, g') = gen_ssavar g in
                              let vm' = M.add fn coq_v vm in
                              let env' = SSATE.add coq_v coq_ty env in
                              let (env'', g'', es'', e) = convert_exp_term es vm' tm' fm sm env' g' fterm in
                              let e' = match_Ebv e in
                              let e'' = QFBV.Bbinop (QFBV.Beq, QFBV.Evar coq_v, e') in
                                (vm', tm', fm, env'', g'', es'', List.rev (e''::bves))
          | TBitVec _ ->  let coq_ty = coq_typ_of_ttyp ty in
                          let (coq_v, g') = gen_ssavar g in
                          let vm' = M.add fn coq_v vm in
                          let env' = SSATE.add coq_v coq_ty env in
                          let (env'', g'', es'', e) = convert_exp_term es vm' tm' fm sm env' g' fterm in
                          let e' = match_Ebv e in
                          let e'' = QFBV.Bbinop (QFBV.Beq, QFBV.Evar coq_v, e') in
                          (vm', tm', fm, env'', g'', es'', List.rev (e''::bves))
          | TFloatVec (eb, sb) -> let tm1 = M.add (fn ^ "_s") (TBitVec 1) tm' in
                                  let tm2 = M.add (fn ^ "_e") (TBitVec eb) tm1 in
                                  let tm3 = M.add (fn ^ "_m") (TBitVec (sb-1)) tm2 in
                                  let coq_ty_s = Tuint 1 in
                                  let coq_ty_e = Tuint eb in
                                  let coq_ty_m = Tuint (sb-1) in
                                  let (coq_v_s, g1) = gen_ssavar g in
                                  let (coq_v_e, g2) = gen_ssavar g1 in
                                  let (coq_v_m, g3) = gen_ssavar g2 in
                                  let vm1 = M.add (fn ^ "_s") coq_v_s vm in
                                  let vm2 = M.add (fn ^ "_e") coq_v_e vm1 in
                                  let vm3 = M.add (fn ^ "_m") coq_v_m vm2 in
                                  let env1 =  SSATE.add coq_v_s coq_ty_s env in
                                  let env2 =  SSATE.add coq_v_e coq_ty_e env1 in
                                  let env3 =  SSATE.add coq_v_m coq_ty_m env2 in
                                  let (env4, g4, es', e) = convert_exp_term es vm3 tm3 fm sm env3 g fterm in
                                  let fe1 = match_Efp e in
                                  let fe2 = Fq2bvq.FEieee754 (eb, (sb-1), QFBV.Evar coq_v_s, QFBV.Evar coq_v_e, QFBV.Evar coq_v_m) in
                                  let e' = Fq2bvq.FBbveq (fe1, fe2) in
                                    (vm3, tm3, fm, env3, g3, List.rev (e'::es'), bves)
          | _ ->  let coq_ty = coq_typ_of_ttyp ty in
                  let (coq_v, g') = gen_ssavar g in
                  let vm' = M.add fn coq_v vm in
                  let env' = SSATE.add coq_v coq_ty env in
                  let (env'', g'', es', e) = convert_fp_bexp_term es vm' tm' fm sm env' g' (make_eq (make_var fn) fterm) in
                    (vm', tm', fm, env'', g'', List.rev (e::es'), bves)
          end
  | _ -> (vm, tm, M.add fn (fargs, fsort, fterm) fm, env, g, es, bves)

let bexps_of_command bves es vm tm fm sm env g c : vm * tm * fm * sm * SSATE.env * int * Fq2bvq.fp_bexp list * QFBV.bexp list =
  match c with
  | CSetLogic _ -> (vm, tm, fm, sm, env, g, es, bves)
  | CSetInfo _ -> (vm, tm, fm, sm, env, g, es, bves)
  | CSetOption _ -> (vm, tm, fm, sm, env, g, es, bves)
  | CDefineSort (sn, sargs, ssort) ->
    let sm' = define_sort sm sn sargs ssort in
    (vm, tm, fm, sm', env, g, es, bves)
  | CDeclareFun (fn, fargs, fsort) ->
     let (vm', tm', fm', env', g') = declare_fun vm tm fm sm env g fn fargs fsort in
     (vm', tm', fm', sm, env', g', es, bves)
  | CDefineFun (fn, fargs, fsort, fterm) ->
     let (vm', tm', fm', env', g', es', bves') = define_fun bves es vm tm fm sm env g fn fargs fsort fterm in
     (vm', tm', fm', sm, env', g', es', bves')
  | CAssert (TApplication (QIdentifier (ISimple v), factuals)) when v = fn_and ->
     let (env', g', es) = List.fold_left (
                              fun (env, g, es) a ->
                              let (env1, g1, es1, e1) = convert_fp_bexp_term es vm tm fm sm env g a in
                              (env1, g1, e1::es1)
                            ) (env, g, es) factuals in
     (vm, tm, fm, sm, env', g', es, bves)
  | CAssert t -> let (env', g', es', e) = convert_fp_bexp_term es vm tm fm sm env g t in
                 (vm, tm, fm, sm, env', g', e::es', bves)
  | CCheckSat -> (vm, tm, fm, sm, env, g, es, bves)
  | CGetModel -> (vm, tm, fm, sm, env, g, es, bves)
  | CExit -> (vm, tm, fm, sm, env, g, es, bves)
  | CComment _ -> (vm, tm, fm, sm, env, g, es, bves)

let is_check_sat c =
  match c with
  | CCheckSat -> true
  | _ -> false

let is_exit c =
  match c with
  | CExit -> true
  | _ -> false

let bexps_of_script vm tm fm sm env g script : vm * tm * fm * sm * SSATE.env * int * Fq2bvq.fp_bexp list * QFBV.bexp list =
  let (cs', ex', vm', tm', fm', sm', env', g', es_rev, bves_rev) =
    List.fold_left (
        fun (cs, ex, vm, tm, fm, sm, env, g, res, rbves) c ->
        let cs_c = is_check_sat c in
        if ex then (cs, ex, vm, tm, fm, sm, env, g, res, rbves)
        else if cs && cs_c then failwith("Multiple check-sat is not supported.")
        else let (vm', tm', fm', sm', env', g', es, bves) = bexps_of_command rbves res vm tm fm sm env g c in
             (cs || cs_c, is_exit c, vm', tm', fm', sm', env', g', es, bves)
      ) (false, false, vm, tm, fm, sm, env, g, [], []) script in
  (vm', tm', fm', sm', env', g', List.rev es_rev, List.rev bves_rev)

let bexps_of_file file : vm * tm * SSATE.env * int * Fq2bvq.fp_bexp list * QFBV.bexp list =
  let vm = M.empty in
  let tm = M.empty in
  let fm = M.empty in
  let sm = M.empty in
  let env = SSATE.empty in
  let g = 0 in
  let (vm', tm', fm', sm', env', g', es, bves) = bexps_of_script vm tm fm sm env g file in
  (vm', tm', env', g', es, bves)

(** Word-blasting *)
let wb_bexps_conj g env fes =
  if Fq2bvq.well_formed_fp_bexps fes env then
    let (((env1, g1), es)) = word_blast_bexps gen_ssavar g [] env fes in
      (env1, g1, es)
  else
    failwith ("Word-blasting illFormed error")

(** Bit-blasting *)

let string_of_ssavar v =
  let (svar, sidx) = Obj.magic v in
  string_of_int (int_of_n svar) ^ " " ^ string_of_int (int_of_n sidx)

(*
 * vm: from var in SMTLIB to var in Coq QFBV
 * env: typing environment in Coq
 * returns a map from QFBV var to its corresponding literals
 *)
let bb_bexps_conj vm env es =
  let _ =
    if !option_debug then
      let _ = M.iter (
                  fun v ssav ->
                  print_endline ("DEBUG: " ^ v ^ " => ssavar " ^ string_of_ssavar ssav)
                ) vm in
      let _ = List.iter (
                  fun (v, ty) ->
                  print_endline ("DEBUG: ssavar " ^ string_of_ssavar v ^ ": BitVec " ^ string_of_ty ty)
                ) (SSATE.elements env) in
      let _ = print_endline ("DEBUG: QF_BV predicates: " ^ String.concat "\n" (List.map string_of_bexp es)) in
      () in
(* if QFBV.well_formed_bexps es env then *)
    if !option_split_conjs then
      let (((m, c), g), cnf) = bit_blast_bexps_hcache_conjs env es in
        (m, cnf)
    else
      let e = make_qfbv_conjs es in
      let ((((m, c), g), cnf), lr) = bit_blast_bexp_hcache_tflatten env init_vm init_hcache init_gen (hash_bexp e) in
      let cnf = CNF.add_prelude ([lr]::cnf) in
        (m, cnf)
(*  else
    raise IllFormedException *)

let bb_file file =
  (* vm: from var in SMTLIB to var in Coq QFBV *)
  let (vm, tm, env, g, fes, bves) = bexps_of_file file in
  let (env1, g1, es) = wb_bexps_conj g env fes in
  let (_, cnf) = bb_bexps_conj vm env (bves@es) in
  cnf


(** Output to DIMACS *)

let coq_string_of_literal l =
  match l with
  | CNF.Pos v -> string_of_int (int_of_pos v)
  | CNF.Neg v -> "-" ^ string_of_int (int_of_pos v)

let coq_output_clause ch c = output_string ch (String.concat " " (List.map coq_string_of_literal c) ^ " 0")

let coq_output_cnf ch cs = List.iter (fun c -> coq_output_clause ch c; output_string ch "\n") cs

let coq_output_dimacs ch cs =
  let nvars = int_of_pos (CNF.max_var_of_cnf cs) in
  let nclauses = int_of_n (CNF.num_clauses cs) in
  let _ = output_string ch ("p cnf " ^ string_of_int nvars ^ " " ^ string_of_int nclauses ^ "\n") in
  let _ = coq_output_cnf ch cs in
  let _ = flush ch in
  (nvars, nclauses)



(** Check SAT *)

type literal_assignments = bool array

type qfbv_assignments = SSAStore.t

type smtlib_assignments = (ttyp * string) M.t

type certified_status = CERTIFIED | UNCERTIFIED

type 'a sat_result = SAT of certified_status * 'a | UNSAT of certified_status

type 'a result = OK of 'a | ERROR of string


(*
 * vm: from var in SMTLIB to var in Coq QFBV
 * env: typing environment in Coq
 *)
let check_sat_bexps_conj vm tm env g es bves =
  let int_of_lit l = int_of_pos (CNF.var_of_lit l) in
  let base_file = tmpfile "coqqffp_" "" in
  let cnf_file =
    match !option_cnf_file with
    | None -> base_file ^ ".cnf"
    | Some fn -> fn in
  let drat_file =
    match !option_drat_file with
    | None -> base_file ^ ".drat"
    | Some fn -> fn in
  let sat_log_file =
    match !option_sat_log_file with
    | None -> base_file ^ ".sat.log"
    | Some fn -> fn in
  let gratl_file =
    match !option_gratl_file with
    | None -> base_file ^ ".gratl"
    | Some fn -> fn in
  let gratp_file =
    match !option_gratp_file with
    | None -> base_file ^ ".gratp"
    | Some fn -> fn in
  let grat_log_file =
    match !option_grat_log_file with
    | None -> base_file ^ ".grat.log"
    | Some fn -> fn in
  let _ = cleanup [base_file] in
  let do_word_blasting g env fes =
    let _ = if !option_verbose then print_string ("Word-blasting: ") in
    let t1 = Unix.gettimeofday() in
    let (env1, g1, es) = wb_bexps_conj g env fes in
    let t2 = Unix.gettimeofday() in
    let _ = if !option_verbose then print_endline ("done [" ^ Printf.sprintf "%.9f" (t2 -. t1) ^ " seconds]") in
      (env1, g1, es) in
  let do_bit_blasting vm env es =
    let _ = if !option_verbose then print_string ("Bit-blasting: ") in
    let t1 = Unix.gettimeofday() in
    let (lm, cnf) = bb_bexps_conj vm env es in
    let t2 = Unix.gettimeofday() in
    let _ = if !option_verbose then print_endline ("done [" ^ Printf.sprintf "%.9f" (t2 -. t1) ^ " seconds]") in
    let _ = if !option_debug then
              List.iter
                (fun (ssavar, lits) ->
                  print_endline ("DEBUG: ssavar " ^ string_of_ssavar ssavar ^ " -> lits "
                                 ^ (String.concat " " (List.map string_of_int (List.map int_of_lit lits))))
                ) (SSAVM.elements lm) in
    (lm, cnf) in
  let do_output_cnf_file cnf =
    let _ = if !option_verbose then print_string ("Saving CNF file: ") in
    let t1 = Unix.gettimeofday() in
    let (nvars, nclauses) =
      let outch = open_out cnf_file in
      let (nvars, nclauses) = coq_output_dimacs outch cnf in
      let _ = close_out outch in
      (nvars, nclauses) in
    let t2 = Unix.gettimeofday() in
    let _ =
      if !option_verbose then
        let _ = print_endline ("done [" ^ Printf.sprintf "%.9f" (t2 -. t1) ^ " seconds]") in
        let _ = print_endline ("CNF file: " ^ cnf_file) in
        let _ = print_endline ("Size of CNF file: " ^ Int64.to_string (Unix.LargeFile.stat cnf_file).Unix.LargeFile.st_size ^ " bytes") in
        let _ = print_endline ("Number of variables in CNF file: " ^ string_of_int nvars) in
        let _ = print_endline ("Number of clauses in CNF file: " ^ string_of_int nclauses) in
        () in
    nvars in
  let do_sat_solving () =
    let _ = if !option_verbose then print_string ("Solving CNF file: ") in
    let t1 = Unix.gettimeofday() in
    let _ =
      let cmd = !option_kissat_path ^ " -q " ^ cnf_file ^ " " ^ drat_file ^ " 2>&1 1>" ^ sat_log_file in
      match Unix.system cmd with
      | Unix.WEXITED 10 -> () (* sat *)
      | Unix.WEXITED 20 -> () (* unsat *)
      | _ -> raise (Failure "Failed to solve CNF file") in
    let t2 = Unix.gettimeofday() in
    let _ =
      if !option_verbose then
        let _ = print_endline ("done [" ^ Printf.sprintf "%.9f" (t2 -. t1) ^ " seconds]") in
        let _ = if Sys.file_exists drat_file then print_endline ("DRAT file: " ^ drat_file ^ "\n"
                                                                 ^ "Size of DRAT file: " ^ Int64.to_string (Unix.LargeFile.stat drat_file).Unix.LargeFile.st_size ^ " bytes") in
        () in
    () in
  let do_parse_sat_result nvars =
    let literal_assignments = ref (Array.make 1 false) in
    let is_unsat =
      let is_unsat = ref None in
      let line = ref "" in
      let inch = open_in sat_log_file in
      let _ =
        try
          while true do
            let _ = line := input_line inch in
            let _ = if !option_debug then print_endline ("DEBUG: SAT result line: " ^ !line) in
            if !line = "s SATISFIABLE" then (literal_assignments := Array.make (nvars + 1) false; is_unsat := Some false)
            else if !line = "s UNSATISFIABLE" then is_unsat := Some true
            else if Str.string_match (Str.regexp "v ") !line 0 then
              let assignments = List.map int_of_string (String.split_on_char ' ' (String.sub !line 2 (String.length !line - 2))) in
              let _ = List.iter (fun v -> !literal_assignments.(abs v) <- (v > 0)) assignments in
              ()
            else raise End_of_file
          done
        with End_of_file -> ()
           | _ -> failwith "Failed to read the SAT solver output file." in
      let _ = close_in inch in
      !is_unsat in
    let _ = if !option_verbose then
              print_endline ("SAT solving result: "
                             ^ match is_unsat with
                               | None -> "error"
                               | Some true -> "unsat"
                               | Some false -> "sat") in
    match is_unsat with
    | None ->
       let _ = Unix.system ("cat " ^ sat_log_file) in
       raise (Failure "Error in SAT solving")
    | Some true -> UNSAT UNCERTIFIED
    | Some false -> SAT (UNCERTIFIED, !literal_assignments) in
  let do_certify_unsat () =
    let _ = if !option_verbose then print_string ("Certifying UNSAT proof: ") in
    let t1 = Unix.gettimeofday() in
    let _ =
      let cmd = !option_gratgen_path ^ " " ^ cnf_file ^ " " ^ drat_file ^ " -b -l " ^ gratl_file ^ " -o " ^ gratp_file ^ " 2>&1 | grep 's VERIFIED' 2>&1 1>/dev/null" in (* &>/dev/null does not work on Linux *)
      match Unix.system cmd with
      | Unix.WEXITED 0 -> () (* grep found *)
      | _ -> raise (Failure "Failed to generate auxiliary lemmas from UNSAT proof") in
    let certified =
      let cmd = !option_gratchk_path ^ " unsat " ^ cnf_file ^ " " ^ gratl_file ^ " " ^ gratp_file ^ " 2>&1 | grep 's VERIFIED UNSAT' 2>&1 1>/dev/null" in (* &>/dev/null does not work on Linux *)
      match Unix.system cmd with
      | Unix.WEXITED 0 -> true (* grep found *)
      | _ -> false in
    let t2 = Unix.gettimeofday() in
    let _ =
      if !option_verbose then
        let _ = print_endline ("done [" ^ Printf.sprintf "%.9f" (t2 -. t1) ^ " seconds]") in
        let _ = if Sys.file_exists gratl_file then print_endline ("GRATL file: " ^ gratl_file ^ "\n"
                                                                  ^ "Size of GRATL file: " ^ Int64.to_string (Unix.LargeFile.stat gratl_file).Unix.LargeFile.st_size ^ " bytes") in
        let _ = if Sys.file_exists gratp_file then print_endline ("GRATP file: " ^ gratp_file ^ "\n"
                                                                  ^ "Size of GRATP file: " ^ Int64.to_string (Unix.LargeFile.stat gratp_file).Unix.LargeFile.st_size ^ " bytes") in
        let _ = print_endline ("UNSAT proof certified: " ^ string_of_bool certified) in
        () in
    certified in
  let qfbv_assignments_of_literal_assignments lm literal_assignments =
    let _ = if !option_debug then Array.iteri (fun i b -> print_endline ("DEBUG: " ^ "cnf var " ^ string_of_int i ^ ": " ^ string_of_bool b)) literal_assignments in
    SSAVM.fold
      (fun ssavar lits store ->
        let bv = List.map (fun l -> literal_assignments.(int_of_lit l)) (lits) in
        let _ = if !option_debug then print_endline ("DEBUG: ssavar " ^ string_of_ssavar ssavar ^ " -> lits "
                                                     ^ (String.concat " " (List.map string_of_int (List.map int_of_lit lits))) ^ ": value " ^ string_of_bits bv) in
        SSAStore.upd ssavar bv store
      ) lm (SSAStore.empty) in
  let smtlib_assignments_of_qfbv_assignments vm tm qfbv_assignments =
    M.mapi (
        fun v coq_v ->
        let ty = M.find v tm in
        let bv = SSAStore.acc coq_v qfbv_assignments in
        let _ = if !option_debug then print_endline ("DEBUG: smtlib var " ^ v ^ " -> ssavar " ^ string_of_ssavar coq_v ^ ": value " ^ string_of_bits bv) in
        (ty, match ty with
             | TBool -> string_of_bool (List.hd bv)
             | TNumeral -> Z.to_string (Z.of_string ("0b" ^ string_of_bits bv))
             | TBitVec w -> "#b" ^ string_of_bits bv
             (* FIXME : Temporarily not supported *)
             | TFloatVec (eb, sb) -> "fp#b" ^ string_of_bits bv
             | TRoundingMode -> "RoundingMode")
      ) vm
  in
  let do_certify_sat es qfbv_assignments =
    let _ = if !option_verbose then print_string ("Certifying SAT assignments: ") in
    let t1 = Unix.gettimeofday() in
    let certified = List.for_all (fun e -> QFBV.eval_bexp e qfbv_assignments) es in
    let t2 = Unix.gettimeofday() in
    let _ =
      if !option_verbose then
        let _ = print_endline ("done [" ^ Printf.sprintf "%.9f" (t2 -. t1) ^ " seconds]") in
        let _ = print_endline ("SAT assignments certified: " ^ string_of_bool certified) in
        () in
    certified in
  let (env', g', res) =
    try
      let (env1, g1, es) = do_word_blasting g env es in
      (* == Bit-blasting == *)
      let (lm, cnf) = do_bit_blasting vm env1 (bves@es) in
      (* == Output CNF file == *)
      let nvars = do_output_cnf_file cnf in
      (* == Run SAT solver == *)
      let _ = do_sat_solving () in
      (* == Parse SAT solving results == *)
      let sat_res = do_parse_sat_result nvars in
      (* == Certify unsat proof or sat assignments == *)
      match sat_res with
      | UNSAT _ ->
         if !option_certify_unsat then
           if do_certify_unsat ()
           then (env1, g1, (OK (UNSAT CERTIFIED)))
           else raise (Failure "Failed to certify UNSAT proof")
         else
           (env1, g1, OK (UNSAT UNCERTIFIED))
      | SAT (_, literal_assignments) ->
         let qfbv_assignments = qfbv_assignments_of_literal_assignments lm literal_assignments in
         let smtlib_assignments = smtlib_assignments_of_qfbv_assignments vm tm qfbv_assignments in
         if !option_certify_sat then
           if do_certify_sat es qfbv_assignments
           then (env1, g1, OK (SAT (CERTIFIED, smtlib_assignments)))
           else raise (Failure "Failed to certify SAT assignments")
         else
           (env1, g1, OK (SAT (UNCERTIFIED, smtlib_assignments)))
    with (Failure msg) -> (env, g, ERROR msg)
       | _ -> (env, g, ERROR "Error") in
  let _ = cleanup [cnf_file; drat_file; sat_log_file; gratl_file; gratp_file; grat_log_file] in
  match res with
  | OK r -> (env', g', r)
  | ERROR msg -> failwith msg

let check_sat_command sat_res_rev bves es vm tm fm sm env g c : smtlib_assignments sat_result list * vm * tm * fm * sm * SSATE.env * int * Fq2bvq.fp_bexp list * QFBV.bexp list =
  match c with
  | CSetLogic _ -> (sat_res_rev, vm, tm, fm, sm, env, g, es, bves)
  | CSetInfo _ -> (sat_res_rev, vm, tm, fm, sm, env, g, es, bves)
  | CSetOption _ -> (sat_res_rev, vm, tm, fm, sm, env, g, es, bves)
  | CDefineSort (sn, sargs, ssort) -> 
    let sm' = define_sort sm sn sargs ssort in
     (sat_res_rev, vm, tm, fm, sm', env, g, es, bves)
  | CDeclareFun (fn, fargs, fsort) ->
     let (vm', tm', fm', env', g') = declare_fun vm tm fm sm env g fn fargs fsort in
     (sat_res_rev, vm', tm', fm', sm, env', g', es, bves)
  | CDefineFun (fn, fargs, fsort, fterm) ->
     let (vm', tm', fm', env', g', es', bves') = define_fun bves es vm tm fm sm env g fn fargs fsort fterm in
     (sat_res_rev, vm', tm', fm', sm, env', g', es', bves')
  | CAssert (TApplication (QIdentifier (ISimple v), factuals)) when v = fn_and ->
     let (env', g', es) = List.fold_left (
                              fun (env, g, es) a ->
                              let (env1, g1, es1, e1) = convert_fp_bexp_term es vm tm fm sm env g a in
                              (env1, g1, e1::es1)
                            ) (env, g, es) factuals in
     (sat_res_rev, vm, tm, fm, sm, env', g', es, bves)
  | CAssert t -> let (env', g', es', e) = convert_fp_bexp_term es vm tm fm sm env g t in
                 (sat_res_rev, vm, tm, fm, sm, env', g', e::es', bves)
  | CCheckSat ->
     let (env', g', sat_res) = check_sat_bexps_conj vm tm env g (List.rev es) (List.rev bves) in
     let _ = print_endline (match sat_res with
                            | UNSAT _ -> "unsat"
                            | SAT _ -> "sat") in
     (sat_res::sat_res_rev, vm, tm, fm, sm, env', g', es, bves)
  | CGetModel ->
     begin
       match sat_res_rev with
       | (SAT (_, model))::_ ->
          let _ = print_string ("(model\n") in
          let _ = M.iter (
                      fun var (typ, value) ->
                      let typ_str =
                        match typ with
                        | TBool -> "Bool"
                        | TNumeral -> "Int"
                        | TBitVec w -> "(_ BitVec " ^ string_of_int w ^ ")"
                        | TFloatVec (eb, sb) -> "(_ FloatingPoint " ^ string_of_int eb ^ " " ^ string_of_int sb ^ ")" 
                        | TRoundingMode -> "RoundingMode" in
                      print_endline ("(define-fun " ^ var ^ " () " ^ typ_str ^ " " ^ value ^ ")")
                    ) model in
          let _ = print_string (")\n") in
          (sat_res_rev, vm, tm, fm, sm, env, g, es, bves)
       | _ -> (sat_res_rev, vm, tm, fm, sm, env, g, es, bves)
     end
  | CExit -> (sat_res_rev, vm, tm, fm, sm, env, g, es, bves)
  | CComment _ -> (sat_res_rev, vm, tm, fm, sm, env, g, es, bves)

let check_sat_script vm tm fm sm env g script =
  let (sat_res_rev, ex', vm', tm', fm', sm', env', g', es_rev, bves_rev) =
    List.fold_left (
        fun (sat_res_rev, ex, vm, tm, fm, sm, env, g, res, rbves) c ->
        if ex then (sat_res_rev, ex, vm, tm, fm, sm, env, g, res, rbves)
        else let (sat_res_rev', vm', tm', fm', sm', env', g', es, bves) = check_sat_command sat_res_rev rbves res vm tm fm sm env g c in
             (sat_res_rev', is_exit c, vm', tm', fm', sm', env', g', es, bves)
      ) ([], false, vm, tm, fm, sm, env, g, [], []) script in
  (List.rev sat_res_rev, vm', tm', fm', sm', env', g', List.rev es_rev, List.rev bves_rev)

let check_sat_file file =
  let vm = M.empty in
  let tm = M.empty in
  let fm = M.empty in
  let sm = M.empty in
  let env = SSATE.empty in
  let g = 0 in
  let (sat_res, vm', tm', fm', sm', env', g', es, bves) = check_sat_script vm tm fm sm env g file in
  (sat_res, vm', tm', env', es, bves)
