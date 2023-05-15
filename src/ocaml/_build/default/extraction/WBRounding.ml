open NBitsDef
open WBCommon
open WBPacking
open Seq
open Ssrnat

(** val rne_exp : QFBV.QFBV.exp **)

let rne_exp =
  QFBV.QFBV.Econst (false :: (false :: (false :: [])))

(** val rna_exp : QFBV.QFBV.exp **)

let rna_exp =
  QFBV.QFBV.Econst (true :: (false :: (false :: [])))

(** val rtp_exp : QFBV.QFBV.exp **)

let rtp_exp =
  QFBV.QFBV.Econst (false :: (true :: (false :: [])))

(** val rtn_exp : QFBV.QFBV.exp **)

let rtn_exp =
  QFBV.QFBV.Econst (true :: (true :: (false :: [])))

(** val rtz_exp : QFBV.QFBV.exp **)

let rtz_exp =
  QFBV.QFBV.Econst (false :: (false :: (true :: [])))

(** val roundUp :
    QFBV.QFBV.exp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp ->
    QFBV.QFBV.bexp -> QFBV.QFBV.bexp **)

let roundUp rm s is_even guard_bit sticky_bit =
  QFBV.QFBV.Bdisj ((QFBV.QFBV.Bdisj ((QFBV.QFBV.Bdisj ((QFBV.QFBV.Bdisj
    ((QFBV.QFBV.Bconj ((QFBV.QFBV.Bconj ((QFBV.QFBV.Bbinop (QFBV.QFBV.Beq,
    rm, rne_exp)), guard_bit)), (QFBV.QFBV.Bdisj (sticky_bit,
    (QFBV.QFBV.Blneg is_even))))), (QFBV.QFBV.Bconj ((QFBV.QFBV.Bbinop
    (QFBV.QFBV.Beq, rm, rna_exp)), guard_bit)))), (QFBV.QFBV.Bconj
    ((QFBV.QFBV.Bconj ((QFBV.QFBV.Bbinop (QFBV.QFBV.Beq, rm, rtp_exp)),
    (QFBV.QFBV.Blneg s))), (QFBV.QFBV.Bdisj (guard_bit, sticky_bit)))))),
    (QFBV.QFBV.Bconj ((QFBV.QFBV.Bconj ((QFBV.QFBV.Bbinop (QFBV.QFBV.Beq, rm,
    rtn_exp)), s)), (QFBV.QFBV.Bdisj (guard_bit, sticky_bit)))))),
    (QFBV.QFBV.Bconj ((QFBV.QFBV.Bbinop (QFBV.QFBV.Beq, rm, rtz_exp)),
    QFBV.QFBV.Bfalse)))

(** val round :
    int -> int -> QFBV.QFBV.exp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp ->
    QFBV.QFBV.bexp -> QFBV.QFBV.exp -> QFBV.QFBV.exp -> int -> int ->
    unpackedbf **)

let round mlen elen rm zs isZero s e m e_size m_size =
  let pre_overflow = is_overflow_bexp mlen elen e e_size in
  let pre_underflow = QFBV.QFBV.Bbinop (QFBV.QFBV.Bslt, e, (QFBV.QFBV.Ebinop
    (QFBV.QFBV.Bsub, (QFBV.QFBV.Eunop ((QFBV.QFBV.Usext
    (subn e_size (unpack_elen mlen elen))),
    (min_subnormal_e_exp mlen elen))), (one_exp e_size))))
  in
  let min_normal_e_exp_ext = QFBV.QFBV.Eunop ((QFBV.QFBV.Usext
    (subn e_size (unpack_elen mlen elen))), (min_normal_e_exp mlen elen))
  in
  let isNormal = QFBV.QFBV.Bbinop (QFBV.QFBV.Bsle, min_normal_e_exp_ext, e) in
  let unrounded_m = QFBV.QFBV.Eunop ((QFBV.QFBV.Uhigh (unpack_mlen mlen)), m)
  in
  let nor_guard_bit_pos =
    subn (subn m_size (unpack_mlen mlen)) (Pervasives.succ 0)
  in
  let nor_guard_bit =
    is_Btrue (QFBV.QFBV.Eunop ((QFBV.QFBV.Uextr (nor_guard_bit_pos,
      nor_guard_bit_pos)), m))
  in
  let nor_sticky_bit = QFBV.QFBV.Blneg
    (is_all_zeros (QFBV.QFBV.Eunop ((QFBV.QFBV.Uextr
      ((subn nor_guard_bit_pos (Pervasives.succ 0)), 0)), m))
      nor_guard_bit_pos)
  in
  let (nor_succ_m, nor_m_ovf) = coq_Bsucc unrounded_m (unpack_mlen mlen) in
  let nor_succ_m0 = QFBV.QFBV.Eite (nor_m_ovf, (QFBV.QFBV.Econst
    (cat (zeros (subn (unpack_mlen mlen) (Pervasives.succ 0))) (true :: []))),
    nor_succ_m)
  in
  let shift_amount = QFBV.QFBV.Ebinop (QFBV.QFBV.Bsub, (QFBV.QFBV.Econst
    (from_Z e_size (max_subnormal_e elen))), e)
  in
  let not_subnor = QFBV.QFBV.Bbinop (QFBV.QFBV.Bsle, shift_amount,
    (zero_exp e_size))
  in
  let subnor_underflow = QFBV.QFBV.Bbinop (QFBV.QFBV.Bsge, shift_amount,
    (QFBV.QFBV.Econst (from_Z e_size (unpack_mlen_Z mlen))))
  in
  let shift_amount0 = QFBV.QFBV.Eite ((QFBV.QFBV.Bdisj (not_subnor,
    subnor_underflow)), (zero_exp e_size), shift_amount)
  in
  let shift_amount1 = QFBV.QFBV.Eunop ((QFBV.QFBV.Uzext
    (subn (unpack_mlen mlen) e_size)), shift_amount0)
  in
  let subnor_guard_pos = QFBV.QFBV.Ebinop (QFBV.QFBV.Bshl,
    (one_exp (unpack_mlen mlen)), shift_amount1)
  in
  let subnor_guard_bit = QFBV.QFBV.Blneg
    (is_all_zeros (QFBV.QFBV.Ebinop (QFBV.QFBV.Band, unrounded_m,
      subnor_guard_pos)) (unpack_mlen mlen))
  in
  let sticky_mask = QFBV.QFBV.Ebinop (QFBV.QFBV.Bsub, subnor_guard_pos,
    (one_exp (unpack_mlen mlen)))
  in
  let subnor_sticky_bit = QFBV.QFBV.Bdisj ((QFBV.QFBV.Bdisj (nor_guard_bit,
    nor_sticky_bit)), (QFBV.QFBV.Blneg
    (is_all_zeros (QFBV.QFBV.Ebinop (QFBV.QFBV.Band, unrounded_m,
      sticky_mask)) (unpack_mlen mlen))))
  in
  let subnor_lsb_pos = QFBV.QFBV.Ebinop (QFBV.QFBV.Bshl, subnor_guard_pos,
    (one_exp (unpack_mlen mlen)))
  in
  let mask = QFBV.QFBV.Ebinop (QFBV.QFBV.Bor, subnor_guard_pos, sticky_mask)
  in
  let inv_mask = QFBV.QFBV.Eunop (QFBV.QFBV.Unot, mask) in
  let subnor_significand = QFBV.QFBV.Ebinop (QFBV.QFBV.Band, unrounded_m,
    inv_mask)
  in
  let subnor_succ_m = QFBV.QFBV.Ebinop (QFBV.QFBV.Badd, subnor_significand,
    subnor_lsb_pos)
  in
  let subnor_m_ovf = is_all_zeros subnor_succ_m (unpack_mlen mlen) in
  let subnor_succ_m0 = QFBV.QFBV.Eite (subnor_m_ovf, (QFBV.QFBV.Econst
    (cat (zeros (subn (unpack_mlen mlen) (Pervasives.succ 0))) (true :: []))),
    subnor_succ_m)
  in
  let guard_bit = coq_Eite_bexp isNormal nor_guard_bit subnor_guard_bit in
  let sticky_bit = coq_Eite_bexp isNormal nor_sticky_bit subnor_sticky_bit in
  let is_even =
    coq_Eite_bexp isNormal (QFBV.QFBV.Blneg (lsb_bexp unrounded_m))
      (is_all_zeros (QFBV.QFBV.Ebinop (QFBV.QFBV.Band, unrounded_m,
        subnor_lsb_pos)) (unpack_mlen mlen))
  in
  let m_up = roundUp rm s is_even guard_bit sticky_bit in
  let rounded_m = QFBV.QFBV.Eite (isNormal, (QFBV.QFBV.Eite (m_up,
    nor_succ_m0, unrounded_m)), (QFBV.QFBV.Eite (m_up, subnor_succ_m0,
    subnor_significand)))
  in
  let ext_e = QFBV.QFBV.Eunop ((QFBV.QFBV.Usext (Pervasives.succ 0)), e) in
  let e_up = QFBV.QFBV.Bconj (m_up,
    (coq_Eite_bexp isNormal nor_m_ovf subnor_m_ovf))
  in
  let correct_e = QFBV.QFBV.Eite (e_up, (QFBV.QFBV.Ebinop (QFBV.QFBV.Badd,
    ext_e, (one_exp (addn e_size (Pervasives.succ 0))))), ext_e)
  in
  let post_overflow =
    is_overflow_bexp mlen elen correct_e (addn e_size (Pervasives.succ 0))
  in
  let post_underflow =
    is_underflow_bexp mlen elen correct_e (addn e_size (Pervasives.succ 0))
  in
  let overflow = coq_Eite_bexp pre_overflow QFBV.QFBV.Btrue post_overflow in
  let underflow = coq_Eite_bexp pre_underflow QFBV.QFBV.Btrue post_underflow
  in
  let rounded_e = QFBV.QFBV.Eunop ((QFBV.QFBV.Ulow (unpack_elen mlen elen)),
    correct_e)
  in
  let returnZero = QFBV.QFBV.Bdisj ((QFBV.QFBV.Bdisj ((QFBV.QFBV.Bdisj
    ((QFBV.QFBV.Bdisj ((QFBV.QFBV.Bbinop (QFBV.QFBV.Beq, rm, rne_exp)),
    (QFBV.QFBV.Bbinop (QFBV.QFBV.Beq, rm, rna_exp)))), (QFBV.QFBV.Bbinop
    (QFBV.QFBV.Beq, rm, rtz_exp)))), (QFBV.QFBV.Bconj ((QFBV.QFBV.Bbinop
    (QFBV.QFBV.Beq, rm, rtp_exp)), s)))), (QFBV.QFBV.Bconj ((QFBV.QFBV.Bbinop
    (QFBV.QFBV.Beq, rm, rtn_exp)), (QFBV.QFBV.Blneg s))))
  in
  let returnInf = QFBV.QFBV.Bdisj ((QFBV.QFBV.Bdisj ((QFBV.QFBV.Bdisj
    ((QFBV.QFBV.Bbinop (QFBV.QFBV.Beq, rm, rne_exp)), (QFBV.QFBV.Bbinop
    (QFBV.QFBV.Beq, rm, rna_exp)))), (QFBV.QFBV.Bconj ((QFBV.QFBV.Bbinop
    (QFBV.QFBV.Beq, rm, rtp_exp)), (QFBV.QFBV.Blneg s))))), (QFBV.QFBV.Bconj
    ((QFBV.QFBV.Bbinop (QFBV.QFBV.Beq, rm, rtn_exp)), s)))
  in
  let inf_flag0 = coq_Eite_bexp overflow returnInf QFBV.QFBV.Bfalse in
  let zero_flag0 =
    coq_Eite_bexp isZero QFBV.QFBV.Btrue
      (coq_Eite_bexp underflow returnZero QFBV.QFBV.Bfalse)
  in
  let nan_flag0 = QFBV.QFBV.Bfalse in
  let un_s0 = coq_Eite_bexp isZero s (coq_Eite_bexp zero_flag0 zs s) in
  let un_e0 = QFBV.QFBV.Eite (isZero, (defaultExponent mlen elen),
    (QFBV.QFBV.Eite (underflow, (QFBV.QFBV.Eite (returnZero,
    (defaultExponent mlen elen), (min_subnormal_e_exp mlen elen))),
    (QFBV.QFBV.Eite (overflow, (QFBV.QFBV.Eite (returnInf,
    (defaultExponent mlen elen), (max_normal_e_exp mlen elen))),
    rounded_e)))))
  in
  let un_m0 = QFBV.QFBV.Eite (isZero, (defaultSignificand mlen),
    (QFBV.QFBV.Eite (underflow, (QFBV.QFBV.Eite (returnZero,
    (defaultSignificand mlen), (min_signficand_exp mlen))), (QFBV.QFBV.Eite
    (overflow, (QFBV.QFBV.Eite (returnInf, (defaultSignificand mlen),
    (max_signficand_exp mlen))), rounded_m)))))
  in
  { inf_flag = inf_flag0; zero_flag = zero_flag0; nan_flag = nan_flag0;
  un_s = un_s0; un_e = un_e0; un_m = un_m0 }
