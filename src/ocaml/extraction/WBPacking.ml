open BinInt
open BinNums
open EqVar
open NBitsDef
open WBCommon
open Seq
open Ssrnat

(** val elen_Z : int -> coq_Z **)

let elen_Z =
  Z.of_nat

(** val unpack_mlen : int -> int **)

let unpack_mlen mlen =
  addn mlen (Pervasives.succ 0)

(** val unpack_mlen_Z : int -> coq_Z **)

let unpack_mlen_Z mlen =
  Z.of_nat (unpack_mlen mlen)

(** val bias : int -> coq_Z **)

let bias elen =
  Z.sub (Z.pow (Zpos (Coq_xO Coq_xH)) (Z.sub (elen_Z elen) (Zpos Coq_xH)))
    (Zpos Coq_xH)

(** val max_normal_e : int -> coq_Z **)

let max_normal_e =
  bias

(** val min_normal_e : int -> coq_Z **)

let min_normal_e elen =
  Z.opp (Z.sub (bias elen) (Zpos Coq_xH))

(** val max_subnormal_e : int -> coq_Z **)

let max_subnormal_e elen =
  Z.opp (bias elen)

(** val min_subnormal_e : int -> int -> coq_Z **)

let min_subnormal_e mlen elen =
  Z.sub (max_subnormal_e elen)
    (Z.sub (unpack_mlen_Z mlen) (Zpos (Coq_xO Coq_xH)))

(** val unpack_elen_Z : int -> int -> coq_Z **)

let unpack_elen_Z mlen elen =
  Z.add (Z.log2_up (Z.abs (min_subnormal_e mlen elen))) (Zpos Coq_xH)

(** val unpack_elen : int -> int -> int **)

let unpack_elen mlen elen =
  Z.to_nat (unpack_elen_Z mlen elen)

(** val bias_exp : int -> int -> QFBV.QFBV.exp **)

let bias_exp mlen elen =
  QFBV.QFBV.Econst (from_Z (unpack_elen mlen elen) (bias elen))

(** val max_normal_e_exp : int -> int -> QFBV.QFBV.exp **)

let max_normal_e_exp mlen elen =
  QFBV.QFBV.Econst (from_Z (unpack_elen mlen elen) (max_normal_e elen))

(** val min_normal_e_exp : int -> int -> QFBV.QFBV.exp **)

let min_normal_e_exp mlen elen =
  QFBV.QFBV.Econst (from_Z (unpack_elen mlen elen) (min_normal_e elen))

(** val max_subnormal_e_exp : int -> int -> QFBV.QFBV.exp **)

let max_subnormal_e_exp mlen elen =
  QFBV.QFBV.Econst (from_Z (unpack_elen mlen elen) (max_subnormal_e elen))

(** val min_subnormal_e_exp : int -> int -> QFBV.QFBV.exp **)

let min_subnormal_e_exp mlen elen =
  QFBV.QFBV.Econst
    (from_Z (unpack_elen mlen elen) (min_subnormal_e mlen elen))

(** val max_signficand_exp : int -> QFBV.QFBV.exp **)

let max_signficand_exp mlen =
  ones_exp (unpack_mlen mlen)

(** val min_signficand_exp : int -> QFBV.QFBV.exp **)

let min_signficand_exp mlen =
  QFBV.QFBV.Econst
    (cat (zeros (subn (unpack_mlen mlen) (Pervasives.succ 0))) (true :: []))

(** val is_in_normal_range_bexp :
    int -> int -> QFBV.QFBV.exp -> int -> QFBV.QFBV.bexp **)

let is_in_normal_range_bexp mlen elen e e_size =
  let max_normal_e_exp_ext = QFBV.QFBV.Eunop ((QFBV.QFBV.Usext
    (subn e_size (unpack_elen mlen elen))), (max_normal_e_exp mlen elen))
  in
  let min_normal_e_exp_ext = QFBV.QFBV.Eunop ((QFBV.QFBV.Usext
    (subn e_size (unpack_elen mlen elen))), (min_normal_e_exp mlen elen))
  in
  QFBV.QFBV.Bconj ((QFBV.QFBV.Bbinop (QFBV.QFBV.Bsle, min_normal_e_exp_ext,
  e)), (QFBV.QFBV.Bbinop (QFBV.QFBV.Bsle, e, max_normal_e_exp_ext)))

(** val is_in_subnormal_range_bexp :
    int -> int -> QFBV.QFBV.exp -> int -> QFBV.QFBV.bexp **)

let is_in_subnormal_range_bexp mlen elen e e_size =
  let max_subnormal_e_exp_ext = QFBV.QFBV.Eunop ((QFBV.QFBV.Usext
    (subn e_size (unpack_elen mlen elen))), (max_subnormal_e_exp mlen elen))
  in
  let min_subnormal_e_exp_ext = QFBV.QFBV.Eunop ((QFBV.QFBV.Usext
    (subn e_size (unpack_elen mlen elen))), (min_subnormal_e_exp mlen elen))
  in
  QFBV.QFBV.Bconj ((QFBV.QFBV.Bbinop (QFBV.QFBV.Bsle,
  min_subnormal_e_exp_ext, e)), (QFBV.QFBV.Bbinop (QFBV.QFBV.Bsle, e,
  max_subnormal_e_exp_ext)))

(** val is_overflow_bexp :
    int -> int -> QFBV.QFBV.exp -> int -> QFBV.QFBV.bexp **)

let is_overflow_bexp mlen elen e e_size =
  let max_normal_e_exp_ext = QFBV.QFBV.Eunop ((QFBV.QFBV.Usext
    (subn e_size (unpack_elen mlen elen))), (max_normal_e_exp mlen elen))
  in
  QFBV.QFBV.Bbinop (QFBV.QFBV.Bsgt, e, max_normal_e_exp_ext)

(** val is_underflow_bexp :
    int -> int -> QFBV.QFBV.exp -> int -> QFBV.QFBV.bexp **)

let is_underflow_bexp mlen elen e e_size =
  let min_subnormal_e_exp_ext = QFBV.QFBV.Eunop ((QFBV.QFBV.Usext
    (subn e_size (unpack_elen mlen elen))), (min_subnormal_e_exp mlen elen))
  in
  QFBV.QFBV.Bbinop (QFBV.QFBV.Bslt, e, min_subnormal_e_exp_ext)

type unpackedbf = { inf_flag : QFBV.QFBV.bexp; zero_flag : QFBV.QFBV.bexp;
                    nan_flag : QFBV.QFBV.bexp; un_s : QFBV.QFBV.bexp;
                    un_e : QFBV.QFBV.exp; un_m : QFBV.QFBV.exp }

(** val make_unpackedbf_var :
    int -> int -> (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list ->
    TypEnv.SSATE.env -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp ->
    QFBV.QFBV.bexp -> QFBV.QFBV.exp -> QFBV.QFBV.exp ->
    ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf **)

let make_unpackedbf_var mlen elen gen_var g es te inf_flag0 zero_flag0 nan_flag0 un_s0 un_e0 un_m0 =
  let (p, inf_flag1) = make_bexp_var gen_var g es te inf_flag0 in
  let (p0, es0) = p in
  let (te0, g0) = p0 in
  let (p1, zero_flag1) = make_bexp_var gen_var g0 es0 te0 zero_flag0 in
  let (p2, es1) = p1 in
  let (te1, g1) = p2 in
  let (p3, nan_flag1) = make_bexp_var gen_var g1 es1 te1 nan_flag0 in
  let (p4, es2) = p3 in
  let (te2, g2) = p4 in
  let (p5, un_s1) = make_bexp_var gen_var g2 es2 te2 un_s0 in
  let (p6, es3) = p5 in
  let (te3, g3) = p6 in
  let (p7, un_e1) =
    make_exp_var gen_var g3 es3 te3 un_e0 (unpack_elen mlen elen)
  in
  let (p8, es4) = p7 in
  let (te4, g4) = p8 in
  let (p9, un_m1) = make_exp_var gen_var g4 es4 te4 un_m0 (unpack_mlen mlen)
  in
  let result = { inf_flag = inf_flag1; zero_flag = zero_flag1; nan_flag =
    nan_flag1; un_s = un_s1; un_e = un_e1; un_m = un_m1 }
  in
  (p9, result)

(** val make_ext_unpackedbf_var :
    (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list -> TypEnv.SSATE.env
    -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp
    -> QFBV.QFBV.exp -> QFBV.QFBV.exp -> int -> int ->
    ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf **)

let make_ext_unpackedbf_var gen_var g es te inf_flag0 zero_flag0 nan_flag0 un_s0 un_e0 un_m0 e_size m_size =
  let (p, inf_flag1) = make_bexp_var gen_var g es te inf_flag0 in
  let (p0, es0) = p in
  let (te0, g0) = p0 in
  let (p1, zero_flag1) = make_bexp_var gen_var g0 es0 te0 zero_flag0 in
  let (p2, es1) = p1 in
  let (te1, g1) = p2 in
  let (p3, nan_flag1) = make_bexp_var gen_var g1 es1 te1 nan_flag0 in
  let (p4, es2) = p3 in
  let (te2, g2) = p4 in
  let (p5, un_s1) = make_bexp_var gen_var g2 es2 te2 un_s0 in
  let (p6, es3) = p5 in
  let (te3, g3) = p6 in
  let (p7, un_e1) = make_exp_var gen_var g3 es3 te3 un_e0 e_size in
  let (p8, es4) = p7 in
  let (te4, g4) = p8 in
  let (p9, un_m1) = make_exp_var gen_var g4 es4 te4 un_m0 m_size in
  let result = { inf_flag = inf_flag1; zero_flag = zero_flag1; nan_flag =
    nan_flag1; un_s = un_s1; un_e = un_e1; un_m = un_m1 }
  in
  (p9, result)

(** val defaultExponent : int -> int -> QFBV.QFBV.exp **)

let defaultExponent mlen elen =
  QFBV.QFBV.Econst (zeros (unpack_elen mlen elen))

(** val defaultExponent_ext : int -> QFBV.QFBV.exp **)

let defaultExponent_ext e_size =
  QFBV.QFBV.Econst (zeros e_size)

(** val defaultSignificand : int -> QFBV.QFBV.exp **)

let defaultSignificand mlen =
  QFBV.QFBV.Econst
    (cat (zeros (subn (unpack_mlen mlen) (Pervasives.succ 0))) (true :: []))

(** val defaultSignificand_ext : int -> QFBV.QFBV.exp **)

let defaultSignificand_ext m_size =
  QFBV.QFBV.Econst
    (cat (zeros (subn m_size (Pervasives.succ 0))) (true :: []))

(** val normalize_shift_amount_sat :
    (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list -> TypEnv.SSATE.env
    -> QFBV.QFBV.exp -> int -> ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp
    list) * QFBV.QFBV.exp **)

let normalize_shift_amount_sat gen_var g es te m m_size =
  let isZero = is_all_zeros m m_size in
  let (p, shift_amount) = make_Evar gen_var g es te m_size in
  let (p0, es0) = p in
  let range_limit = QFBV.QFBV.Bconj ((QFBV.QFBV.Bbinop (QFBV.QFBV.Buge,
    shift_amount, (zero_exp m_size))), (QFBV.QFBV.Bbinop (QFBV.QFBV.Bult,
    shift_amount, (QFBV.QFBV.Econst (from_nat m_size m_size)))))
  in
  let leading_one =
    msb_bexp (QFBV.QFBV.Ebinop (QFBV.QFBV.Bshl, m, shift_amount))
  in
  let init_mask = ones_exp m_size in
  let shifted_mask = QFBV.QFBV.Ebinop (QFBV.QFBV.Blshr, init_mask,
    shift_amount)
  in
  let mask = QFBV.QFBV.Eunop (QFBV.QFBV.Unot, shifted_mask) in
  let leading_zeros = QFBV.QFBV.Bbinop (QFBV.QFBV.Beq, (QFBV.QFBV.Ebinop
    (QFBV.QFBV.Band, mask, m)), (zero_exp m_size))
  in
  let limits = QFBV.QFBV.Bdisj (isZero, (QFBV.QFBV.Bconj ((QFBV.QFBV.Bconj
    (range_limit, leading_one)), leading_zeros)))
  in
  let es1 = limits :: es0 in ((p0, es1), shift_amount)

(** val normalize_sat :
    (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list -> TypEnv.SSATE.env
    -> QFBV.QFBV.exp -> QFBV.QFBV.exp -> int -> int ->
    (((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp
    list) * QFBV.QFBV.exp) * QFBV.QFBV.exp **)

let normalize_sat gen_var g es te e m e_size m_size =
  let (p, shift_amount) = normalize_shift_amount_sat gen_var g es te m m_size
  in
  let normal_m = QFBV.QFBV.Ebinop (QFBV.QFBV.Bshl, m, shift_amount) in
  let e_shift_amount = QFBV.QFBV.Eunop ((QFBV.QFBV.Uextr
    ((subn e_size (Pervasives.succ 0)), 0)), shift_amount)
  in
  let normal_e = QFBV.QFBV.Ebinop (QFBV.QFBV.Bsub, e, e_shift_amount) in
  ((p, normal_e), normal_m)

(** val normalize :
    (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list -> TypEnv.SSATE.env
    -> QFBV.QFBV.exp -> QFBV.QFBV.exp -> int -> int ->
    (((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp
    list) * QFBV.QFBV.exp) * QFBV.QFBV.exp **)

let normalize =
  normalize_sat

(** val unpack :
    int -> int -> (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list ->
    TypEnv.SSATE.env -> QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.exp ->
    ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf **)

let unpack mlen elen gen_var g es te s e m =
  let returnInf = QFBV.QFBV.Bconj ((is_all_ones e elen),
    (is_all_zeros m mlen))
  in
  let returnZero = QFBV.QFBV.Bconj ((is_all_zeros e elen),
    (is_all_zeros m mlen))
  in
  let returnNormal = QFBV.QFBV.Bconj ((QFBV.QFBV.Blneg
    (is_all_zeros e elen)), (QFBV.QFBV.Blneg (is_all_ones e elen)))
  in
  let returnNaN = QFBV.QFBV.Bconj ((is_all_ones e elen), (QFBV.QFBV.Blneg
    (is_all_zeros m mlen)))
  in
  let extended_e = QFBV.QFBV.Eunop ((QFBV.QFBV.Uzext
    (subn (unpack_elen mlen elen) elen)), e)
  in
  let nor_m = QFBV.QFBV.Ebinop (QFBV.QFBV.Bconcat, (QFBV.QFBV.Econst
    (true :: [])), m)
  in
  let nor_e = QFBV.QFBV.Ebinop (QFBV.QFBV.Bsub, extended_e, (QFBV.QFBV.Econst
    (from_Z (unpack_elen mlen elen) (bias elen))))
  in
  let subnor_m_base = QFBV.QFBV.Ebinop (QFBV.QFBV.Bconcat, (QFBV.QFBV.Econst
    (false :: [])), m)
  in
  let subnor_e_base = min_normal_e_exp mlen elen in
  let (p, subnor_m) =
    normalize gen_var g es te subnor_e_base subnor_m_base
      (unpack_elen mlen elen) (unpack_mlen mlen)
  in
  let (p0, subnor_e) = p in
  let (p1, es0) = p0 in
  let (te0, g0) = p1 in
  let un_s0 = is_Btrue s in
  let un_e0 = QFBV.QFBV.Eite ((QFBV.QFBV.Bdisj ((QFBV.QFBV.Bdisj (returnInf,
    returnZero)), returnNaN)), (defaultExponent mlen elen), (QFBV.QFBV.Eite
    (returnNormal, nor_e, subnor_e)))
  in
  let un_m0 = QFBV.QFBV.Eite ((QFBV.QFBV.Bdisj ((QFBV.QFBV.Bdisj (returnInf,
    returnZero)), returnNaN)), (defaultSignificand mlen), (QFBV.QFBV.Eite
    (returnNormal, nor_m, subnor_m)))
  in
  make_unpackedbf_var mlen elen gen_var g0 es0 te0 returnInf returnZero
    returnNaN un_s0 un_e0 un_m0

(** val pack :
    int -> int -> unpackedbf ->
    (QFBV.QFBV.exp * QFBV.QFBV.exp) * QFBV.QFBV.exp **)

let pack mlen elen bf =
  let s = bf.un_s in
  let s_exp = QFBV.QFBV.Eite (s, (QFBV.QFBV.Econst (true :: [])),
    (QFBV.QFBV.Econst (false :: [])))
  in
  let e = bf.un_e in
  let m = bf.un_m in
  let returnInf = bf.inf_flag in
  let returnZero = bf.zero_flag in
  let returnNaN = bf.nan_flag in
  let returnNormal =
    is_in_normal_range_bexp mlen elen e (unpack_elen mlen elen)
  in
  let unsigned_e = QFBV.QFBV.Ebinop (QFBV.QFBV.Badd, e, (bias_exp mlen elen))
  in
  let nor_packed_e = QFBV.QFBV.Eunop ((QFBV.QFBV.Ulow elen), unsigned_e) in
  let nor_packed_m = QFBV.QFBV.Eunop ((QFBV.QFBV.Ulow mlen), m) in
  let shift_amount = QFBV.QFBV.Ebinop (QFBV.QFBV.Bsub,
    (min_normal_e_exp mlen elen), e)
  in
  let shift_amount0 =
    if leq (unpack_elen mlen elen) (unpack_mlen mlen)
    then QFBV.QFBV.Eunop ((QFBV.QFBV.Usext
           (subn (unpack_mlen mlen) (unpack_elen mlen elen))), shift_amount)
    else QFBV.QFBV.Eunop ((QFBV.QFBV.Ulow (unpack_mlen mlen)), shift_amount)
  in
  let shr_m = QFBV.QFBV.Ebinop (QFBV.QFBV.Blshr, m, shift_amount0) in
  let subnor_packed_m = QFBV.QFBV.Eunop ((QFBV.QFBV.Ulow mlen), shr_m) in
  let zero_e = zero_exp elen in
  let packed_s = QFBV.QFBV.Eite (returnNaN, coq_Btrue_exp, s_exp) in
  let packed_e = QFBV.QFBV.Eite ((QFBV.QFBV.Bdisj (returnNaN, returnInf)),
    (ones_exp elen), (QFBV.QFBV.Eite (returnZero, (zero_exp elen),
    (QFBV.QFBV.Eite (returnNormal, nor_packed_e, zero_e)))))
  in
  let packed_m = QFBV.QFBV.Eite (returnNaN, (ones_exp mlen), (QFBV.QFBV.Eite
    ((QFBV.QFBV.Bdisj (returnInf, returnZero)), (zero_exp mlen),
    (QFBV.QFBV.Eite (returnNormal, nor_packed_m, subnor_packed_m)))))
  in
  ((packed_s, packed_e), packed_m)
