open EqVar
open WBCommon
open WBPacking

(** val abs_unpackedbf :
    int -> int -> (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list ->
    TypEnv.SSATE.env -> unpackedbf ->
    ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf **)

let abs_unpackedbf mlen elen gen_var g es te bf =
  let inf_flag0 = coq_Eite_bexp bf.nan_flag QFBV.QFBV.Bfalse bf.inf_flag in
  let zero_flag0 = coq_Eite_bexp bf.nan_flag QFBV.QFBV.Bfalse bf.zero_flag in
  let un_s0 = coq_Eite_bexp bf.nan_flag QFBV.QFBV.Btrue QFBV.QFBV.Bfalse in
  let un_e0 = QFBV.QFBV.Eite (bf.nan_flag, (defaultExponent mlen elen),
    bf.un_e)
  in
  let un_m0 = QFBV.QFBV.Eite (bf.nan_flag, (defaultSignificand mlen), bf.un_m)
  in
  let (p, un_e1) = make_exp_var gen_var g es te un_e0 (unpack_elen mlen elen)
  in
  let (p0, es0) = p in
  let (te0, g0) = p0 in
  let (p1, un_m1) = make_exp_var gen_var g0 es0 te0 un_m0 (unpack_mlen mlen)
  in
  let result = { inf_flag = inf_flag0; zero_flag = zero_flag0; nan_flag =
    bf.nan_flag; un_s = un_s0; un_e = un_e1; un_m = un_m1 }
  in
  (p1, result)

(** val neg_unpackedbf :
    int -> int -> (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list ->
    TypEnv.SSATE.env -> unpackedbf ->
    ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf **)

let neg_unpackedbf mlen elen gen_var g es te bf =
  let inf_flag0 = coq_Eite_bexp bf.nan_flag QFBV.QFBV.Bfalse bf.inf_flag in
  let zero_flag0 = coq_Eite_bexp bf.nan_flag QFBV.QFBV.Bfalse bf.zero_flag in
  let un_s0 =
    coq_Eite_bexp bf.nan_flag QFBV.QFBV.Btrue (QFBV.QFBV.Blneg bf.un_s)
  in
  let un_e0 = QFBV.QFBV.Eite (bf.nan_flag, (defaultExponent mlen elen),
    bf.un_e)
  in
  let un_m0 = QFBV.QFBV.Eite (bf.nan_flag, (defaultSignificand mlen), bf.un_m)
  in
  let (p, un_e1) = make_exp_var gen_var g es te un_e0 (unpack_elen mlen elen)
  in
  let (p0, es0) = p in
  let (te0, g0) = p0 in
  let (p1, un_m1) = make_exp_var gen_var g0 es0 te0 un_m0 (unpack_mlen mlen)
  in
  let result = { inf_flag = inf_flag0; zero_flag = zero_flag0; nan_flag =
    bf.nan_flag; un_s = un_s0; un_e = un_e1; un_m = un_m1 }
  in
  (p1, result)
