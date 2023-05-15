open EqVar
open WBCommon
open WBPacking
open WBRounding
open Ssrnat

(** val xorSign : QFBV.QFBV.bexp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp **)

let xorSign =
  coq_Bxor_bexp

(** val mul_unpackbf :
    int -> int -> (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list ->
    TypEnv.SSATE.env -> QFBV.QFBV.exp -> unpackedbf -> unpackedbf ->
    ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf **)

let mul_unpackbf mlen elen gen_var g es te rm bf1 bf2 =
  let eitherNaN = QFBV.QFBV.Bdisj (bf1.nan_flag, bf2.nan_flag) in
  let inf_zero = QFBV.QFBV.Bdisj ((QFBV.QFBV.Bconj (bf1.inf_flag,
    bf2.zero_flag)), (QFBV.QFBV.Bconj (bf1.zero_flag, bf2.inf_flag)))
  in
  let returnNaN = QFBV.QFBV.Bdisj (eitherNaN, inf_zero) in
  let returnInf = QFBV.QFBV.Bdisj (bf1.inf_flag, bf2.inf_flag) in
  let returnZero = QFBV.QFBV.Bdisj (bf1.zero_flag, bf2.zero_flag) in
  let s1 = bf1.un_s in
  let e1 = bf1.un_e in
  let m1 = bf1.un_m in
  let s2 = bf2.un_s in
  let e2 = bf2.un_e in
  let m2 = bf2.un_m in
  let s = xorSign s1 s2 in
  let ext_m1 = QFBV.QFBV.Eunop ((QFBV.QFBV.Uzext (unpack_mlen mlen)), m1) in
  let ext_m2 = QFBV.QFBV.Eunop ((QFBV.QFBV.Uzext (unpack_mlen mlen)), m2) in
  let m_size = addn (unpack_mlen mlen) (unpack_mlen mlen) in
  let product_m = QFBV.QFBV.Ebinop (QFBV.QFBV.Bmul, ext_m1, ext_m2) in
  let has_leading_one = msb_bexp product_m in
  let normal_product_m = QFBV.QFBV.Eite (has_leading_one, product_m,
    (QFBV.QFBV.Ebinop (QFBV.QFBV.Bshl, product_m, (one_exp m_size))))
  in
  let ext_e1 = QFBV.QFBV.Eunop ((QFBV.QFBV.Usext (Pervasives.succ 0)), e1) in
  let ext_e2 = QFBV.QFBV.Eunop ((QFBV.QFBV.Usext (Pervasives.succ 0)), e2) in
  let e_size = addn (unpack_elen mlen elen) (Pervasives.succ 0) in
  let sum_e = coq_Badc has_leading_one ext_e1 ext_e2 e_size in
  let rounded_result =
    round mlen elen rm s returnZero s sum_e normal_product_m e_size m_size
  in
  let inf_flag0 =
    coq_Eite_bexp returnNaN QFBV.QFBV.Bfalse
      (coq_Eite_bexp returnInf QFBV.QFBV.Btrue
        (coq_Eite_bexp returnZero QFBV.QFBV.Bfalse rounded_result.inf_flag))
  in
  let zero_flag0 =
    coq_Eite_bexp returnNaN QFBV.QFBV.Bfalse
      (coq_Eite_bexp returnInf QFBV.QFBV.Bfalse
        (coq_Eite_bexp returnZero QFBV.QFBV.Btrue rounded_result.zero_flag))
  in
  let nan_flag0 = coq_Eite_bexp returnNaN QFBV.QFBV.Btrue QFBV.QFBV.Bfalse in
  let un_s0 =
    coq_Eite_bexp returnNaN QFBV.QFBV.Btrue
      (coq_Eite_bexp (QFBV.QFBV.Bdisj (returnInf, returnZero)) s
        rounded_result.un_s)
  in
  let un_e0 = QFBV.QFBV.Eite ((QFBV.QFBV.Bdisj ((QFBV.QFBV.Bdisj (returnNaN,
    returnInf)), returnZero)), (defaultExponent mlen elen),
    rounded_result.un_e)
  in
  let un_m0 = QFBV.QFBV.Eite ((QFBV.QFBV.Bdisj ((QFBV.QFBV.Bdisj (returnNaN,
    returnInf)), returnZero)), (defaultSignificand mlen), rounded_result.un_m)
  in
  make_unpackedbf_var mlen elen gen_var g es te inf_flag0 zero_flag0
    nan_flag0 un_s0 un_e0 un_m0
