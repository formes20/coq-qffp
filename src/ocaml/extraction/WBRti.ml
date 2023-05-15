open BinInt
open EqVar
open NBitsDef
open WBCommon
open WBPacking
open WBRounding
open Ssrnat

(** val roundToIntegral_unpackbf :
    int -> int -> (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list ->
    TypEnv.SSATE.env -> QFBV.QFBV.exp -> unpackedbf ->
    ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf **)

let roundToIntegral_unpackbf mlen elen gen_var g es te rm bf =
  let s = bf.un_s in
  let e = bf.un_e in
  let m = bf.un_m in
  let mlen_exp = QFBV.QFBV.Econst
    (from_Z (unpack_elen mlen elen) (Z.of_nat mlen))
  in
  let returnSelf = QFBV.QFBV.Bdisj ((QFBV.QFBV.Bdisj ((QFBV.QFBV.Bdisj
    ((QFBV.QFBV.Bbinop (QFBV.QFBV.Bsge, e, mlen_exp)), bf.inf_flag)),
    bf.zero_flag)), bf.nan_flag)
  in
  let ext_e = QFBV.QFBV.Eunop ((QFBV.QFBV.Usext (Pervasives.succ 0)), e) in
  let ext_mlen_exp = QFBV.QFBV.Eunop ((QFBV.QFBV.Usext (Pervasives.succ 0)),
    mlen_exp)
  in
  let round_index = QFBV.QFBV.Ebinop (QFBV.QFBV.Bsub, ext_mlen_exp, ext_e) in
  let round_index0 = QFBV.QFBV.Eite ((QFBV.QFBV.Bbinop (QFBV.QFBV.Bsle,
    round_index,
    (zero_exp (addn (unpack_elen mlen elen) (Pervasives.succ 0))))),
    (zero_exp (addn (unpack_elen mlen elen) (Pervasives.succ 0))),
    round_index)
  in
  let unpack_mlen_plus1_exp = QFBV.QFBV.Econst
    (from_Z (addn (unpack_elen mlen elen) (Pervasives.succ 0))
      (Z.of_nat (addn (unpack_mlen mlen) (Pervasives.succ 0))))
  in
  let round_index1 = QFBV.QFBV.Eite ((QFBV.QFBV.Bbinop (QFBV.QFBV.Bsge,
    round_index0, unpack_mlen_plus1_exp)), unpack_mlen_plus1_exp,
    round_index0)
  in
  let round_index_size = addn (unpack_elen mlen elen) (Pervasives.succ 0) in
  let ext_m = QFBV.QFBV.Ebinop (QFBV.QFBV.Bconcat, (QFBV.QFBV.Eunop
    ((QFBV.QFBV.Uzext (Pervasives.succ (Pervasives.succ 0))), m)),
    (zero_exp (Pervasives.succ (Pervasives.succ 0))))
  in
  let m_size =
    addn (unpack_mlen mlen) (Pervasives.succ (Pervasives.succ
      (Pervasives.succ (Pervasives.succ 0))))
  in
  let round_index2 = QFBV.QFBV.Eunop ((QFBV.QFBV.Uzext
    (subn m_size round_index_size)), round_index1)
  in
  let origin_round_pos = QFBV.QFBV.Ebinop (QFBV.QFBV.Bshl, (one_exp m_size),
    round_index2)
  in
  let guard_pos = QFBV.QFBV.Ebinop (QFBV.QFBV.Bshl, origin_round_pos,
    (one_exp m_size))
  in
  let round_pos = QFBV.QFBV.Ebinop (QFBV.QFBV.Bshl, guard_pos,
    (one_exp m_size))
  in
  let sticky_mask = QFBV.QFBV.Ebinop (QFBV.QFBV.Bsub, guard_pos,
    (one_exp m_size))
  in
  let is_even =
    is_all_zeros (QFBV.QFBV.Ebinop (QFBV.QFBV.Band, round_pos, ext_m)) m_size
  in
  let guard_bit = QFBV.QFBV.Blneg
    (is_all_zeros (QFBV.QFBV.Ebinop (QFBV.QFBV.Band, guard_pos, ext_m))
      m_size)
  in
  let sticky_bit = QFBV.QFBV.Blneg
    (is_all_zeros (QFBV.QFBV.Ebinop (QFBV.QFBV.Band, sticky_mask, ext_m))
      m_size)
  in
  let m_up = roundUp rm s is_even guard_bit sticky_bit in
  let rounded_m = QFBV.QFBV.Ebinop (QFBV.QFBV.Badd, ext_m, (QFBV.QFBV.Eite
    (m_up, round_pos, (zero_exp m_size))))
  in
  let mask = QFBV.QFBV.Ebinop (QFBV.QFBV.Bor, guard_pos, sticky_mask) in
  let reverse_mask = QFBV.QFBV.Eunop (QFBV.QFBV.Unot, mask) in
  let masked_m = QFBV.QFBV.Ebinop (QFBV.QFBV.Band, rounded_m, reverse_mask) in
  let top_bit = QFBV.QFBV.Eunop ((QFBV.QFBV.Uextr
    ((subn m_size (Pervasives.succ 0)), (subn m_size (Pervasives.succ 0)))),
    rounded_m)
  in
  let ovf_bit = QFBV.QFBV.Eunop ((QFBV.QFBV.Uextr
    ((subn m_size (Pervasives.succ (Pervasives.succ 0))),
    (subn m_size (Pervasives.succ (Pervasives.succ 0))))), rounded_m)
  in
  let correct_e = QFBV.QFBV.Eite ((is_Btrue top_bit),
    (zero_exp (unpack_elen mlen elen)), (QFBV.QFBV.Eite ((is_Btrue ovf_bit),
    (QFBV.QFBV.Ebinop (QFBV.QFBV.Badd, e,
    (one_exp (unpack_elen mlen elen)))), e)))
  in
  let extract_m = QFBV.QFBV.Eunop ((QFBV.QFBV.Uextr
    ((addn (unpack_mlen mlen) (Pervasives.succ 0)), (Pervasives.succ
    (Pervasives.succ 0)))), masked_m)
  in
  let correct_m = QFBV.QFBV.Ebinop (QFBV.QFBV.Bor, extract_m,
    (QFBV.QFBV.Ebinop (QFBV.QFBV.Bconcat, (QFBV.QFBV.Ebinop (QFBV.QFBV.Bor,
    top_bit, ovf_bit)),
    (zero_exp (subn (unpack_mlen mlen) (Pervasives.succ 0))))))
  in
  let inf_flag0 = coq_Eite_bexp returnSelf bf.inf_flag QFBV.QFBV.Bfalse in
  let zero_flag0 =
    coq_Eite_bexp returnSelf bf.zero_flag
      (coq_Eite_bexp (is_all_zeros correct_m (unpack_mlen mlen))
        QFBV.QFBV.Btrue QFBV.QFBV.Bfalse)
  in
  let nan_flag0 = coq_Eite_bexp returnSelf bf.nan_flag QFBV.QFBV.Bfalse in
  let un_e0 = QFBV.QFBV.Eite (returnSelf, e, (QFBV.QFBV.Eite (zero_flag0,
    (defaultExponent mlen elen), correct_e)))
  in
  let un_m0 = QFBV.QFBV.Eite (returnSelf, m, (QFBV.QFBV.Eite (zero_flag0,
    (defaultSignificand mlen), correct_m)))
  in
  make_unpackedbf_var mlen elen gen_var g es te inf_flag0 zero_flag0
    nan_flag0 s un_e0 un_m0
