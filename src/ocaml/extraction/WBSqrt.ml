open EqVar
open NBitsDef
open WBCommon
open WBPacking
open WBRounding
open Seq
open Ssrnat

(** val full_fixedpoint_sqrt_sat :
    (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list -> TypEnv.SSATE.env
    -> QFBV.QFBV.exp -> int -> (((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp
    list) * QFBV.QFBV.exp) * QFBV.QFBV.bexp **)

let full_fixedpoint_sqrt_sat gen_var g es te comp result_size =
  let (p, sqrt_m) = make_Evar gen_var g es te result_size in
  let (p0, es0) = p in
  let range_limit = QFBV.QFBV.Bbinop (QFBV.QFBV.Buge, sqrt_m,
    (QFBV.QFBV.Econst
    (cat (zeros (subn result_size (Pervasives.succ 0))) (true :: []))))
  in
  let ext_sqrt_m = QFBV.QFBV.Eunop ((QFBV.QFBV.Uzext result_size), sqrt_m) in
  let lower_product = QFBV.QFBV.Ebinop (QFBV.QFBV.Bmul, ext_sqrt_m,
    ext_sqrt_m)
  in
  let succ_sqrt_m = QFBV.QFBV.Ebinop (QFBV.QFBV.Badd, sqrt_m,
    (one_exp result_size))
  in
  let ext_succ_sqrt_m = QFBV.QFBV.Eunop ((QFBV.QFBV.Uzext result_size),
    succ_sqrt_m)
  in
  let higher_product = QFBV.QFBV.Ebinop (QFBV.QFBV.Bmul, ext_succ_sqrt_m,
    ext_succ_sqrt_m)
  in
  let sqrt_limit =
    coq_Eite_bexp (is_all_ones sqrt_m result_size) (QFBV.QFBV.Bbinop
      (QFBV.QFBV.Bule, lower_product, comp)) (QFBV.QFBV.Bconj
      ((QFBV.QFBV.Bbinop (QFBV.QFBV.Bule, lower_product, comp)),
      (QFBV.QFBV.Bbinop (QFBV.QFBV.Bugt, higher_product, comp))))
  in
  let remainder_bit = QFBV.QFBV.Blneg (QFBV.QFBV.Bbinop (QFBV.QFBV.Beq,
    lower_product, comp))
  in
  let es1 = range_limit :: (sqrt_limit :: es0) in
  (((p0, es1), sqrt_m), remainder_bit)

(** val fixedpoint_sqrtB :
    (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list -> TypEnv.SSATE.env
    -> QFBV.QFBV.exp -> int -> (((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp
    list) * QFBV.QFBV.exp) * QFBV.QFBV.bexp **)

let fixedpoint_sqrtB gen_var g es te bs bs_size =
  let ext_bs = QFBV.QFBV.Ebinop (QFBV.QFBV.Bconcat, bs,
    (zero_exp (subn bs_size (Pervasives.succ (Pervasives.succ 0)))))
  in
  full_fixedpoint_sqrt_sat gen_var g es te ext_bs
    (subn bs_size (Pervasives.succ 0))

(** val sqrt_unpackbf :
    int -> int -> (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list ->
    TypEnv.SSATE.env -> QFBV.QFBV.exp -> unpackedbf ->
    ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf **)

let sqrt_unpackbf mlen elen gen_var g es te rm bf =
  let returnNaN = QFBV.QFBV.Bconj ((QFBV.QFBV.Bdisj (bf.nan_flag, bf.un_s)),
    (QFBV.QFBV.Blneg bf.zero_flag))
  in
  let returnInf = QFBV.QFBV.Bconj (bf.inf_flag, (QFBV.QFBV.Blneg bf.un_s)) in
  let returnZero = bf.zero_flag in
  let s = bf.un_s in
  let e = bf.un_e in
  let m = bf.un_m in
  let is_e_odd = lsb_bexp e in
  let e_size = unpack_elen mlen elen in
  let halved_e = QFBV.QFBV.Ebinop (QFBV.QFBV.Bashr, e, (one_exp e_size)) in
  let ext_m = QFBV.QFBV.Ebinop (QFBV.QFBV.Bconcat, (QFBV.QFBV.Eunop
    ((QFBV.QFBV.Uzext (Pervasives.succ 0)), m)),
    (zero_exp (Pervasives.succ 0)))
  in
  let m_size = addn (unpack_mlen mlen) (Pervasives.succ (Pervasives.succ 0))
  in
  let aligned_m = QFBV.QFBV.Eite (is_e_odd, (QFBV.QFBV.Ebinop
    (QFBV.QFBV.Bshl, ext_m, (one_exp m_size))), ext_m)
  in
  let (p, remainder_bit) = fixedpoint_sqrtB gen_var g es te aligned_m m_size
  in
  let (p0, sqrt_m) = p in
  let (p1, es0) = p0 in
  let (te0, g0) = p1 in
  let sticky_bit = QFBV.QFBV.Eite (remainder_bit,
    (one_exp (Pervasives.succ 0)), (zero_exp (Pervasives.succ 0)))
  in
  let sticky_m = QFBV.QFBV.Ebinop (QFBV.QFBV.Bconcat, sqrt_m, sticky_bit) in
  let rounded_result =
    round mlen elen rm QFBV.QFBV.Bfalse returnZero QFBV.QFBV.Bfalse halved_e
      sticky_m e_size m_size
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
      (coq_Eite_bexp returnZero s rounded_result.un_s)
  in
  let un_e0 = QFBV.QFBV.Eite ((QFBV.QFBV.Bdisj ((QFBV.QFBV.Bdisj (returnNaN,
    returnInf)), returnZero)), (defaultExponent mlen elen),
    rounded_result.un_e)
  in
  let un_m0 = QFBV.QFBV.Eite ((QFBV.QFBV.Bdisj ((QFBV.QFBV.Bdisj (returnNaN,
    returnInf)), returnZero)), (defaultSignificand mlen), rounded_result.un_m)
  in
  make_unpackedbf_var mlen elen gen_var g0 es0 te0 inf_flag0 zero_flag0
    nan_flag0 un_s0 un_e0 un_m0
