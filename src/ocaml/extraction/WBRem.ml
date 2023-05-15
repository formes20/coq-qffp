open BinInt
open BinNums
open Datatypes
open EqVar
open NBitsDef
open WBAddSub
open WBCommon
open WBPacking
open WBRounding
open Ssrnat

(** val divide_step :
    QFBV.QFBV.exp -> QFBV.QFBV.exp -> int -> QFBV.QFBV.exp * QFBV.QFBV.bexp **)

let divide_step remainder divider bs_size =
  let can_subtract = QFBV.QFBV.Bbinop (QFBV.QFBV.Buge, remainder, divider) in
  let subed_remainder = QFBV.QFBV.Ebinop (QFBV.QFBV.Bsub, remainder, divider)
  in
  let next_remainder = QFBV.QFBV.Eite (can_subtract, (QFBV.QFBV.Ebinop
    (QFBV.QFBV.Bshl, subed_remainder, (one_exp bs_size))), (QFBV.QFBV.Ebinop
    (QFBV.QFBV.Bshl, remainder, (one_exp bs_size))))
  in
  (next_remainder, can_subtract)

(** val divide_loop :
    (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list -> TypEnv.SSATE.env
    -> QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.exp -> int -> int -> int
    -> ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * QFBV.QFBV.exp **)

let rec divide_loop gen_var g es te remainder divider iter_exp bs_size iter_size loop_iter =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> (((te, g), es), remainder))
    (fun loop_iter' ->
    let next_remainder = fst (divide_step remainder divider bs_size) in
    let needPrevious = QFBV.QFBV.Bbinop (QFBV.QFBV.Bsge, iter_exp,
      (QFBV.QFBV.Econst (from_nat iter_size loop_iter)))
    in
    let active_remainder = QFBV.QFBV.Eite (needPrevious, next_remainder,
      remainder)
    in
    let (p, active_remainder0) =
      make_exp_var gen_var g es te active_remainder bs_size
    in
    let (p0, es0) = p in
    let (te0, g0) = p0 in
    divide_loop gen_var g0 es0 te0 active_remainder0 divider iter_exp bs_size
      iter_size loop_iter')
    loop_iter

(** val remrne_unpackbf :
    int -> int -> (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list ->
    TypEnv.SSATE.env -> unpackedbf -> unpackedbf ->
    ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf **)

let remrne_unpackbf mlen elen gen_var g es te bf1 bf2 =
  let eitherNaN = QFBV.QFBV.Bdisj (bf1.nan_flag, bf2.nan_flag) in
  let returnNaN = QFBV.QFBV.Bdisj ((QFBV.QFBV.Bdisj (eitherNaN,
    bf1.inf_flag)), bf2.zero_flag)
  in
  let rightInf = QFBV.QFBV.Bconj ((QFBV.QFBV.Blneg bf1.inf_flag),
    bf2.inf_flag)
  in
  let leftZero = QFBV.QFBV.Bconj (bf1.zero_flag, (QFBV.QFBV.Blneg
    bf2.nan_flag))
  in
  let returnLeft = QFBV.QFBV.Bdisj (rightInf, leftZero) in
  let s1 = bf1.un_s in
  let e1 = bf1.un_e in
  let m1 = bf1.un_m in
  let s2 = bf2.un_s in
  let e2 = bf2.un_e in
  let m2 = bf2.un_m in
  let ext_e1 = QFBV.QFBV.Eunop ((QFBV.QFBV.Usext (Pervasives.succ 0)), e1) in
  let ext_e2 = QFBV.QFBV.Eunop ((QFBV.QFBV.Usext (Pervasives.succ 0)), e2) in
  let e_diff = QFBV.QFBV.Ebinop (QFBV.QFBV.Bsub, ext_e1, ext_e2) in
  let ed_size = addn (unpack_elen mlen elen) (Pervasives.succ 0) in
  let ext_m1 = QFBV.QFBV.Eunop ((QFBV.QFBV.Uzext (Pervasives.succ 0)), m1) in
  let ext_m2 = QFBV.QFBV.Eunop ((QFBV.QFBV.Uzext (Pervasives.succ 0)), m2) in
  let ext_m_size = addn (unpack_mlen mlen) (Pervasives.succ 0) in
  let max_e_diff =
    Z.to_nat (Z.sub (max_normal_e elen) (min_subnormal_e mlen elen))
  in
  let (p, r) =
    divide_loop gen_var g es te ext_m1 ext_m2 e_diff ext_m_size ed_size
      max_e_diff
  in
  let (p0, es0) = p in
  let (te0, g0) = p0 in
  let lsbRoundActive = QFBV.QFBV.Bbinop (QFBV.QFBV.Bsge, e_diff,
    (zero_exp ed_size))
  in
  let needPrevious = QFBV.QFBV.Bbinop (QFBV.QFBV.Bsgt, e_diff,
    (zero_exp ed_size))
  in
  let r0 = QFBV.QFBV.Eite (needPrevious, r, ext_m1) in
  let (dsr_result, dsr_rembit) = divide_step r0 ext_m2 ext_m_size in
  let intergerEven = QFBV.QFBV.Bdisj ((QFBV.QFBV.Blneg lsbRoundActive),
    (QFBV.QFBV.Blneg dsr_rembit))
  in
  let guardRoundActive = QFBV.QFBV.Bbinop (QFBV.QFBV.Bsge, e_diff,
    (QFBV.QFBV.Econst (from_Z ed_size (Zneg Coq_xH))))
  in
  let rm1 = QFBV.QFBV.Eite (lsbRoundActive, dsr_result, ext_m1) in
  let (dsrg_result, dsrg_rembit) = divide_step rm1 ext_m2 ext_m_size in
  let guard_bit = QFBV.QFBV.Bconj (guardRoundActive, dsrg_rembit) in
  let sticky_bit = QFBV.QFBV.Blneg
    (is_all_zeros (QFBV.QFBV.Eite (guardRoundActive, dsrg_result, ext_m1))
      ext_m_size)
  in
  let m = QFBV.QFBV.Eunop ((QFBV.QFBV.Uhigh (unpack_mlen mlen)), dsr_result)
  in
  let returnZero = is_all_zeros m (unpack_mlen mlen) in
  let (p1, normal_m) =
    normalize gen_var g0 es0 te0 e2 m (unpack_elen mlen elen)
      (unpack_mlen mlen)
  in
  let (p2, normal_e) = p1 in
  let (p3, es1) = p2 in
  let (te1, g1) = p3 in
  let candidate_e = QFBV.QFBV.Eite (lsbRoundActive, (QFBV.QFBV.Eite
    (returnZero, (defaultExponent mlen elen), normal_e)), e1)
  in
  let candidate_m = QFBV.QFBV.Eite (lsbRoundActive, (QFBV.QFBV.Eite
    (returnZero, (defaultSignificand mlen), normal_m)), m1)
  in
  let (p4, candidate_e0) =
    make_exp_var gen_var g1 es1 te1 candidate_e (unpack_elen mlen elen)
  in
  let (p5, es2) = p4 in
  let (te2, g2) = p5 in
  let (p6, candidate_m0) =
    make_exp_var gen_var g2 es2 te2 candidate_m (unpack_mlen mlen)
  in
  let (p7, es3) = p6 in
  let (te3, g3) = p7 in
  let candidate_result = { inf_flag = QFBV.QFBV.Bfalse; zero_flag =
    returnZero; nan_flag = QFBV.QFBV.Bfalse; un_s = s1; un_e = candidate_e0;
    un_m = candidate_m0 }
  in
  let bonusSubtract = QFBV.QFBV.Bconj (guard_bit, (QFBV.QFBV.Bdisj
    (sticky_bit, (QFBV.QFBV.Blneg intergerEven))))
  in
  let (p8, subed_result) =
    add_unpackbf' mlen elen gen_var g3 es3 te3 rne_exp candidate_result bf2
      (coq_Bxor_bexp s1 s2)
  in
  let (p9, es4) = p8 in
  let (te4, g4) = p9 in
  let inf_flag0 =
    coq_Eite_bexp returnNaN QFBV.QFBV.Bfalse
      (coq_Eite_bexp returnLeft bf1.inf_flag
        (coq_Eite_bexp bonusSubtract subed_result.inf_flag
          candidate_result.inf_flag))
  in
  let zero_flag0 =
    coq_Eite_bexp returnNaN QFBV.QFBV.Bfalse
      (coq_Eite_bexp returnLeft bf1.zero_flag
        (coq_Eite_bexp bonusSubtract subed_result.zero_flag
          candidate_result.zero_flag))
  in
  let nan_flag0 = coq_Eite_bexp returnNaN QFBV.QFBV.Btrue QFBV.QFBV.Bfalse in
  let un_s0 =
    coq_Eite_bexp returnNaN QFBV.QFBV.Btrue
      (coq_Eite_bexp returnLeft s1
        (coq_Eite_bexp bonusSubtract subed_result.un_s candidate_result.un_s))
  in
  let un_e0 = QFBV.QFBV.Eite (returnNaN, (defaultExponent mlen elen),
    (QFBV.QFBV.Eite (returnLeft, e1, (QFBV.QFBV.Eite (bonusSubtract,
    subed_result.un_e, candidate_result.un_e)))))
  in
  let un_m0 = QFBV.QFBV.Eite (returnNaN, (defaultSignificand mlen),
    (QFBV.QFBV.Eite (returnLeft, m1, (QFBV.QFBV.Eite (bonusSubtract,
    subed_result.un_m, candidate_result.un_m)))))
  in
  make_unpackedbf_var mlen elen gen_var g4 es4 te4 inf_flag0 zero_flag0
    nan_flag0 un_s0 un_e0 un_m0
