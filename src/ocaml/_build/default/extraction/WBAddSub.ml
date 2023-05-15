open EqVar
open WBCommon
open WBPacking
open WBRounding
open Ssrnat

(** val addSign :
    QFBV.QFBV.exp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp **)

let addSign rm s1 s2 =
  coq_Eite_bexp (QFBV.QFBV.Bbinop (QFBV.QFBV.Beq, rm, rtn_exp))
    (QFBV.QFBV.Bdisj (s1, s2)) (QFBV.QFBV.Bconj (s1, s2))

(** val subSign :
    QFBV.QFBV.exp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp **)

let subSign rm s1 s2 =
  coq_Eite_bexp (QFBV.QFBV.Bbinop (QFBV.QFBV.Beq, rm, rtn_exp))
    (QFBV.QFBV.Bdisj (s1, (QFBV.QFBV.Blneg s2))) (QFBV.QFBV.Bconj (s1,
    (QFBV.QFBV.Blneg s2)))

(** val sticky_ashrB :
    QFBV.QFBV.exp -> QFBV.QFBV.exp -> int -> int ->
    QFBV.QFBV.exp * QFBV.QFBV.bexp **)

let sticky_ashrB m shift_amount m_size sa_size =
  let shift_amount0 = QFBV.QFBV.Eunop ((QFBV.QFBV.Usext
    (subn m_size sa_size)), shift_amount)
  in
  let mask = QFBV.QFBV.Ebinop (QFBV.QFBV.Bshl, (ones_exp m_size),
    shift_amount0)
  in
  let reverse_mask = QFBV.QFBV.Eunop (QFBV.QFBV.Unot, mask) in
  let sticky_bits = QFBV.QFBV.Ebinop (QFBV.QFBV.Band, m, reverse_mask) in
  let sticky_bit = QFBV.QFBV.Blneg (QFBV.QFBV.Bbinop (QFBV.QFBV.Beq,
    sticky_bits, (zero_exp m_size)))
  in
  let aligned_m = QFBV.QFBV.Ebinop (QFBV.QFBV.Bashr, m, shift_amount0) in
  (aligned_m, sticky_bit)

(** val add_unpackbf' :
    int -> int -> (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list ->
    TypEnv.SSATE.env -> QFBV.QFBV.exp -> unpackedbf -> unpackedbf ->
    QFBV.QFBV.bexp -> ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp
    list) * unpackedbf **)

let add_unpackbf' mlen elen gen_var g es te rm bf1 bf2 is_add =
  let eitherNaN = QFBV.QFBV.Bdisj (bf1.nan_flag, bf2.nan_flag) in
  let bothInf = QFBV.QFBV.Bconj (bf1.inf_flag, bf2.inf_flag) in
  let diffSign = coq_Bxor_bexp bf1.un_s bf2.un_s in
  let compatableSign = coq_Bxor_bexp is_add diffSign in
  let returnNaN = QFBV.QFBV.Bdisj (eitherNaN, (QFBV.QFBV.Bconj (bothInf,
    (QFBV.QFBV.Blneg compatableSign))))
  in
  let returnInf = QFBV.QFBV.Bdisj ((QFBV.QFBV.Bdisj ((QFBV.QFBV.Bconj
    (bothInf, compatableSign)), (QFBV.QFBV.Bconj (bf1.inf_flag,
    (QFBV.QFBV.Blneg bf2.inf_flag))))), (QFBV.QFBV.Bconj ((QFBV.QFBV.Blneg
    bf1.inf_flag), bf2.inf_flag)))
  in
  let inf_sign =
    coq_Eite_bexp bf1.inf_flag bf1.un_s
      (coq_Bxor_bexp is_add (QFBV.QFBV.Blneg bf2.un_s))
  in
  let returnZero = QFBV.QFBV.Bconj (bf1.zero_flag, bf2.zero_flag) in
  let zero_sign =
    coq_Eite_bexp is_add (addSign rm bf1.un_s bf2.un_s)
      (subSign rm bf1.un_s bf2.un_s)
  in
  let returnLeft = QFBV.QFBV.Bconj ((QFBV.QFBV.Blneg bf1.zero_flag),
    bf2.zero_flag)
  in
  let returnRight = QFBV.QFBV.Bconj (bf1.zero_flag, (QFBV.QFBV.Blneg
    bf2.zero_flag))
  in
  let s1 = bf1.un_s in
  let e1 = bf1.un_e in
  let m1 = bf1.un_m in
  let s2 = bf2.un_s in
  let e2 = bf2.un_e in
  let m2 = bf2.un_m in
  let is_sign_add = coq_Bxor_bexp (coq_Bxor_bexp s1 s2) is_add in
  let ext_e1 = QFBV.QFBV.Eunop ((QFBV.QFBV.Usext (Pervasives.succ 0)), e1) in
  let ext_e2 = QFBV.QFBV.Eunop ((QFBV.QFBV.Usext (Pervasives.succ 0)), e2) in
  let e_size = addn (unpack_elen mlen elen) (Pervasives.succ 0) in
  let e_diff = QFBV.QFBV.Ebinop (QFBV.QFBV.Bsub, ext_e1, ext_e2) in
  let left_e_larger = QFBV.QFBV.Blneg (msb_bexp e_diff) in
  let abs_e_diff = QFBV.QFBV.Eite (left_e_larger, e_diff, (QFBV.QFBV.Eunop
    (QFBV.QFBV.Uneg, e_diff)))
  in
  let larger_e = QFBV.QFBV.Eite (left_e_larger, ext_e1, ext_e2) in
  let e_diff_is_zero = QFBV.QFBV.Bbinop (QFBV.QFBV.Beq, e_diff,
    (zero_exp e_size))
  in
  let e_diff_is_one = QFBV.QFBV.Bbinop (QFBV.QFBV.Beq, e_diff,
    (one_exp e_size))
  in
  let left_larger = QFBV.QFBV.Bconj (left_e_larger,
    (coq_Eite_bexp e_diff_is_zero (QFBV.QFBV.Bbinop (QFBV.QFBV.Buge, m1, m2))
      QFBV.QFBV.Btrue))
  in
  let larger_m = QFBV.QFBV.Eite (left_larger, m1, m2) in
  let smaller_m = QFBV.QFBV.Eite (left_larger, m2, m1) in
  let ext_m1 = QFBV.QFBV.Ebinop (QFBV.QFBV.Bconcat, (QFBV.QFBV.Eunop
    ((QFBV.QFBV.Uzext (Pervasives.succ 0)), larger_m)),
    (zero_exp (Pervasives.succ (Pervasives.succ 0))))
  in
  let ext_m2 = QFBV.QFBV.Ebinop (QFBV.QFBV.Bconcat, (QFBV.QFBV.Eunop
    ((QFBV.QFBV.Uzext (Pervasives.succ 0)), smaller_m)),
    (zero_exp (Pervasives.succ (Pervasives.succ 0))))
  in
  let m_size =
    addn (unpack_mlen mlen) (Pervasives.succ (Pervasives.succ
      (Pervasives.succ 0)))
  in
  let result_sign =
    coq_Eite_bexp left_larger s1 (coq_Bxor_bexp (QFBV.QFBV.Blneg is_add) s2)
  in
  let negated_m2 = QFBV.QFBV.Eite (is_sign_add, ext_m2, (QFBV.QFBV.Eunop
    (QFBV.QFBV.Uneg, ext_m2)))
  in
  let (aligned_m2, shifted_stickyBit) =
    sticky_ashrB negated_m2 abs_e_diff m_size e_size
  in
  let sum = QFBV.QFBV.Ebinop (QFBV.QFBV.Badd, ext_m1, aligned_m2) in
  let top_bit = msb_bexp sum in
  let aligned_bit =
    is_Btrue (QFBV.QFBV.Eunop ((QFBV.QFBV.Uextr
      ((subn m_size (Pervasives.succ (Pervasives.succ 0))),
      (subn m_size (Pervasives.succ (Pervasives.succ 0))))), sum))
  in
  let lower_bit =
    is_Btrue (QFBV.QFBV.Eunop ((QFBV.QFBV.Uextr
      ((subn m_size (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))),
      (subn m_size (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))),
      sum))
  in
  let cancel = QFBV.QFBV.Bconj ((QFBV.QFBV.Blneg top_bit), (QFBV.QFBV.Blneg
    aligned_bit))
  in
  let minor_cancel = QFBV.QFBV.Bconj (cancel, lower_bit) in
  let major_cancel = QFBV.QFBV.Bconj (cancel, (QFBV.QFBV.Blneg lower_bit)) in
  let full_cancel = QFBV.QFBV.Bconj (major_cancel, (is_all_zeros sum m_size))
  in
  let returnZero0 = QFBV.QFBV.Bdisj (returnZero, full_cancel) in
  let aligned_sum = QFBV.QFBV.Eite (minor_cancel, (QFBV.QFBV.Ebinop
    (QFBV.QFBV.Bshl, sum, (one_exp m_size))), (QFBV.QFBV.Eite (top_bit,
    (QFBV.QFBV.Ebinop (QFBV.QFBV.Blshr, sum, (one_exp m_size))), sum)))
  in
  let correct_e = QFBV.QFBV.Eite (minor_cancel, (QFBV.QFBV.Ebinop
    (QFBV.QFBV.Bsub, larger_e, (one_exp e_size))), (QFBV.QFBV.Eite (top_bit,
    (QFBV.QFBV.Ebinop (QFBV.QFBV.Badd, larger_e, (one_exp e_size))),
    larger_e)))
  in
  let aligned_stickyBit =
    coq_Eite_bexp top_bit (lsb_bexp sum) QFBV.QFBV.Bfalse
  in
  let sticky_bit_is_zero = QFBV.QFBV.Bdisj (e_diff_is_zero, e_diff_is_one) in
  let sticky_bit_mask = QFBV.QFBV.Eite ((QFBV.QFBV.Bdisj (sticky_bit_is_zero,
    major_cancel)), (zero_exp m_size), (QFBV.QFBV.Eite ((QFBV.QFBV.Bdisj
    (shifted_stickyBit, aligned_stickyBit)), (one_exp m_size),
    (zero_exp m_size))))
  in
  let sticky_sum = QFBV.QFBV.Ebinop (QFBV.QFBV.Bor, aligned_sum,
    sticky_bit_mask)
  in
  let contract_sum = QFBV.QFBV.Eunop ((QFBV.QFBV.Ulow
    (subn m_size (Pervasives.succ 0))), sticky_sum)
  in
  let m_size0 = subn m_size (Pervasives.succ 0) in
  let (p, correct_e0) = make_exp_var gen_var g es te correct_e e_size in
  let (p0, es0) = p in
  let (te0, g0) = p0 in
  let (p1, contract_sum0) =
    make_exp_var gen_var g0 es0 te0 contract_sum m_size0
  in
  let (p2, es1) = p1 in
  let (te1, g1) = p2 in
  let (p3, normal_m) =
    normalize gen_var g1 es1 te1 correct_e0 contract_sum0 e_size m_size0
  in
  let (p4, normal_e) = p3 in
  let (p5, es2) = p4 in
  let (te2, g2) = p5 in
  let rounded_result =
    round mlen elen rm zero_sign returnZero0 result_sign normal_e normal_m
      e_size m_size0
  in
  let inf_flag0 =
    coq_Eite_bexp returnLeft bf1.inf_flag
      (coq_Eite_bexp returnRight bf2.inf_flag
        (coq_Eite_bexp returnNaN QFBV.QFBV.Bfalse
          (coq_Eite_bexp returnInf QFBV.QFBV.Btrue
            (coq_Eite_bexp returnZero0 QFBV.QFBV.Bfalse
              rounded_result.inf_flag))))
  in
  let zero_flag0 =
    coq_Eite_bexp returnLeft bf1.zero_flag
      (coq_Eite_bexp returnRight bf2.zero_flag
        (coq_Eite_bexp returnNaN QFBV.QFBV.Bfalse
          (coq_Eite_bexp returnInf QFBV.QFBV.Bfalse
            (coq_Eite_bexp returnZero0 QFBV.QFBV.Btrue
              rounded_result.zero_flag))))
  in
  let nan_flag0 = coq_Eite_bexp returnNaN QFBV.QFBV.Btrue QFBV.QFBV.Bfalse in
  let un_s0 =
    coq_Eite_bexp returnNaN QFBV.QFBV.Btrue
      (coq_Eite_bexp returnLeft s1
        (coq_Eite_bexp returnRight
          (coq_Eite_bexp is_add s2 (QFBV.QFBV.Blneg s2))
          (coq_Eite_bexp returnInf inf_sign
            (coq_Eite_bexp returnZero0 zero_sign rounded_result.un_s))))
  in
  let un_e0 = QFBV.QFBV.Eite (returnLeft, e1, (QFBV.QFBV.Eite (returnRight,
    e2, (QFBV.QFBV.Eite ((QFBV.QFBV.Bdisj ((QFBV.QFBV.Bdisj (returnNaN,
    returnInf)), returnZero0)), (defaultExponent mlen elen),
    rounded_result.un_e)))))
  in
  let un_m0 = QFBV.QFBV.Eite (returnLeft, m1, (QFBV.QFBV.Eite (returnRight,
    m2, (QFBV.QFBV.Eite ((QFBV.QFBV.Bdisj ((QFBV.QFBV.Bdisj (returnNaN,
    returnInf)), returnZero0)), (defaultSignificand mlen),
    rounded_result.un_m)))))
  in
  make_unpackedbf_var mlen elen gen_var g2 es2 te2 inf_flag0 zero_flag0
    nan_flag0 un_s0 un_e0 un_m0

(** val add_unpackbf :
    int -> int -> (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list ->
    TypEnv.SSATE.env -> QFBV.QFBV.exp -> unpackedbf -> unpackedbf ->
    ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf **)

let add_unpackbf mlen elen gen_var g es te rm bf1 bf2 =
  add_unpackbf' mlen elen gen_var g es te rm bf1 bf2 QFBV.QFBV.Btrue

(** val sub_unpackbf :
    int -> int -> (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list ->
    TypEnv.SSATE.env -> QFBV.QFBV.exp -> unpackedbf -> unpackedbf ->
    ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf **)

let sub_unpackbf mlen elen gen_var g es te rm bf1 bf2 =
  add_unpackbf' mlen elen gen_var g es te rm bf1 bf2 QFBV.QFBV.Bfalse
