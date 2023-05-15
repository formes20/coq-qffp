open EqVar
open WBCommon
open WBPacking
open WBRounding
open Ssrnat

(** val fixedpoint_Budiv :
    QFBV.QFBV.exp -> QFBV.QFBV.exp -> int -> QFBV.QFBV.exp * QFBV.QFBV.bexp **)

let fixedpoint_Budiv bs1 bs2 bs_size =
  let ext_bs1 = QFBV.QFBV.Ebinop (QFBV.QFBV.Bconcat, bs1,
    (zero_exp (subn bs_size (Pervasives.succ 0))))
  in
  let ext_bs2 = QFBV.QFBV.Eunop ((QFBV.QFBV.Uzext
    (subn bs_size (Pervasives.succ 0))), bs2)
  in
  let quo = QFBV.QFBV.Ebinop (QFBV.QFBV.Bdiv, ext_bs1, ext_bs2) in
  let rem = QFBV.QFBV.Ebinop (QFBV.QFBV.Bmod, ext_bs1, ext_bs2) in
  let contract_quo = QFBV.QFBV.Eunop ((QFBV.QFBV.Ulow bs_size), quo) in
  let has_rem = QFBV.QFBV.Blneg
    (is_all_zeros rem (subn (addn bs_size bs_size) (Pervasives.succ 0)))
  in
  (contract_quo, has_rem)

(** val div_unpackbf :
    int -> int -> (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list ->
    TypEnv.SSATE.env -> QFBV.QFBV.exp -> unpackedbf -> unpackedbf ->
    ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf **)

let div_unpackbf mlen elen gen_var g es te rm bf1 bf2 =
  let eitherNaN = QFBV.QFBV.Bdisj (bf1.nan_flag, bf2.nan_flag) in
  let bothInf = QFBV.QFBV.Bconj (bf1.inf_flag, bf2.inf_flag) in
  let bothZero = QFBV.QFBV.Bconj (bf1.zero_flag, bf2.zero_flag) in
  let returnNaN = QFBV.QFBV.Bdisj ((QFBV.QFBV.Bdisj (eitherNaN, bothInf)),
    bothZero)
  in
  let leftInf = QFBV.QFBV.Bconj ((QFBV.QFBV.Bconj (bf1.inf_flag,
    (QFBV.QFBV.Blneg bf2.inf_flag))), (QFBV.QFBV.Blneg bf2.nan_flag))
  in
  let rightZero = QFBV.QFBV.Bconj ((QFBV.QFBV.Bconj ((QFBV.QFBV.Blneg
    bf1.zero_flag), (QFBV.QFBV.Blneg bf1.nan_flag))), bf2.zero_flag)
  in
  let returnInf = QFBV.QFBV.Bdisj (leftInf, rightZero) in
  let leftZero = QFBV.QFBV.Bconj ((QFBV.QFBV.Bconj (bf1.zero_flag,
    (QFBV.QFBV.Blneg bf2.zero_flag))), (QFBV.QFBV.Blneg bf2.nan_flag))
  in
  let rightInf = QFBV.QFBV.Bconj ((QFBV.QFBV.Bconj ((QFBV.QFBV.Blneg
    bf1.inf_flag), (QFBV.QFBV.Blneg bf1.nan_flag))), bf2.inf_flag)
  in
  let returnZero = QFBV.QFBV.Bdisj (leftZero, rightInf) in
  let s1 = bf1.un_s in
  let e1 = bf1.un_e in
  let m1 = bf1.un_m in
  let s2 = bf2.un_s in
  let e2 = bf2.un_e in
  let m2 = bf2.un_m in
  let result_sign = coq_Bxor_bexp s1 s2 in
  let ext_e1 = QFBV.QFBV.Eunop ((QFBV.QFBV.Usext (Pervasives.succ
    (Pervasives.succ 0))), e1)
  in
  let ext_e2 = QFBV.QFBV.Eunop ((QFBV.QFBV.Usext (Pervasives.succ
    (Pervasives.succ 0))), e2)
  in
  let e_size =
    addn (unpack_elen mlen elen) (Pervasives.succ (Pervasives.succ 0))
  in
  let sub_e = QFBV.QFBV.Ebinop (QFBV.QFBV.Bsub, ext_e1, ext_e2) in
  let ext_m1 = QFBV.QFBV.Ebinop (QFBV.QFBV.Bconcat, m1,
    (zero_exp (Pervasives.succ (Pervasives.succ 0))))
  in
  let ext_m2 = QFBV.QFBV.Ebinop (QFBV.QFBV.Bconcat, m2,
    (zero_exp (Pervasives.succ (Pervasives.succ 0))))
  in
  let m_size = addn (unpack_mlen mlen) (Pervasives.succ (Pervasives.succ 0))
  in
  let (div_m, rem_sticky_bit) = fixedpoint_Budiv ext_m1 ext_m2 m_size in
  let cancel = QFBV.QFBV.Blneg (msb_bexp div_m) in
  let aligned_m = QFBV.QFBV.Eite (cancel, (QFBV.QFBV.Ebinop (QFBV.QFBV.Bshl,
    div_m, (one_exp m_size))), div_m)
  in
  let aligned_e = QFBV.QFBV.Eite (cancel, (QFBV.QFBV.Ebinop (QFBV.QFBV.Bsub,
    sub_e, (one_exp e_size))), sub_e)
  in
  let mask = QFBV.QFBV.Eite (rem_sticky_bit, (one_exp m_size),
    (zero_exp m_size))
  in
  let sticky_m = QFBV.QFBV.Ebinop (QFBV.QFBV.Bor, aligned_m, mask) in
  let rounded_result =
    round mlen elen rm result_sign returnZero result_sign aligned_e sticky_m
      e_size m_size
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
      (coq_Eite_bexp (QFBV.QFBV.Bdisj (returnInf, returnZero)) result_sign
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
