open EqVar
open WBClassify
open WBCommon
open WBPacking

(** val eq_unpackedbf :
    int -> int -> unpackedbf -> unpackedbf -> QFBV.QFBV.bexp **)

let eq_unpackedbf _ _ bf1 bf2 =
  let neitherNaN = QFBV.QFBV.Bconj ((QFBV.QFBV.Blneg bf1.nan_flag),
    (QFBV.QFBV.Blneg bf2.nan_flag))
  in
  let bothZero = QFBV.QFBV.Bconj (bf1.zero_flag, bf2.zero_flag) in
  let flagsEqual = QFBV.QFBV.Bconj ((QFBV.QFBV.Bconj
    ((coq_Biff bf1.inf_flag bf2.inf_flag),
    (coq_Biff bf1.zero_flag bf2.zero_flag))), (coq_Biff bf1.un_s bf2.un_s))
  in
  QFBV.QFBV.Bconj (neitherNaN, (QFBV.QFBV.Bdisj (bothZero, (QFBV.QFBV.Bconj
  ((QFBV.QFBV.Bconj (flagsEqual, (QFBV.QFBV.Bbinop (QFBV.QFBV.Beq, bf1.un_e,
  bf2.un_e)))), (QFBV.QFBV.Bbinop (QFBV.QFBV.Beq, bf1.un_m, bf2.un_m)))))))

(** val lt_unpackedbf :
    int -> int -> unpackedbf -> unpackedbf -> QFBV.QFBV.bexp **)

let lt_unpackedbf mlen elen bf1 bf2 =
  let neitherNaN = QFBV.QFBV.Bconj ((QFBV.QFBV.Blneg
    (isNaN_unpackedbf mlen elen bf1)), (QFBV.QFBV.Blneg
    (isNaN_unpackedbf mlen elen bf2)))
  in
  let leftZero = QFBV.QFBV.Bconj ((QFBV.QFBV.Bconj
    ((isZero_unpackedbf mlen elen bf1), (QFBV.QFBV.Blneg
    (isZero_unpackedbf mlen elen bf2)))), (QFBV.QFBV.Blneg bf2.un_s))
  in
  let rightZero = QFBV.QFBV.Bconj ((QFBV.QFBV.Bconj ((QFBV.QFBV.Blneg
    (isZero_unpackedbf mlen elen bf1)), (isZero_unpackedbf mlen elen bf2))),
    bf1.un_s)
  in
  let leftNegInf = QFBV.QFBV.Bconj ((isNegInfinite_unpackedbf mlen elen bf1),
    (QFBV.QFBV.Blneg (isNegInfinite_unpackedbf mlen elen bf2)))
  in
  let rightPosInf = QFBV.QFBV.Bconj
    ((isPosInfinite_unpackedbf mlen elen bf2), (QFBV.QFBV.Blneg
    (isPosInfinite_unpackedbf mlen elen bf1)))
  in
  let s1 = bf1.un_s in
  let e1 = bf1.un_e in
  let m1 = bf1.un_m in
  let s2 = bf2.un_s in
  let e2 = bf2.un_e in
  let m2 = bf2.un_m in
  let leftNegRightPos = QFBV.QFBV.Bconj (s1, (QFBV.QFBV.Blneg s2)) in
  let bothNeg = QFBV.QFBV.Bconj ((QFBV.QFBV.Bconj (s1, s2)), (QFBV.QFBV.Bdisj
    ((QFBV.QFBV.Bbinop (QFBV.QFBV.Bsgt, e1, e2)), (QFBV.QFBV.Bconj
    ((QFBV.QFBV.Bbinop (QFBV.QFBV.Beq, e1, e2)), (QFBV.QFBV.Bbinop
    (QFBV.QFBV.Bsgt, m1, m2)))))))
  in
  let bothPos = QFBV.QFBV.Bconj ((QFBV.QFBV.Bconj ((QFBV.QFBV.Blneg s1),
    (QFBV.QFBV.Blneg s2))), (QFBV.QFBV.Bdisj ((QFBV.QFBV.Bbinop
    (QFBV.QFBV.Bslt, e1, e2)), (QFBV.QFBV.Bconj ((QFBV.QFBV.Bbinop
    (QFBV.QFBV.Beq, e1, e2)), (QFBV.QFBV.Bbinop (QFBV.QFBV.Bslt, m1, m2)))))))
  in
  let bothSuborNor = QFBV.QFBV.Bconj ((QFBV.QFBV.Bconj
    ((isSuborNor_unpackedbf mlen elen bf1),
    (isSuborNor_unpackedbf mlen elen bf2))), (QFBV.QFBV.Bdisj
    ((QFBV.QFBV.Bdisj (leftNegRightPos, bothNeg)), bothPos)))
  in
  QFBV.QFBV.Bconj (neitherNaN, (QFBV.QFBV.Bdisj ((QFBV.QFBV.Bdisj
  ((QFBV.QFBV.Bdisj ((QFBV.QFBV.Bdisj (leftZero, rightZero)), leftNegInf)),
  rightPosInf)), bothSuborNor)))

(** val le_unpackedbf :
    int -> int -> unpackedbf -> unpackedbf -> QFBV.QFBV.bexp **)

let le_unpackedbf mlen elen bf1 bf2 =
  QFBV.QFBV.Bdisj ((eq_unpackedbf mlen elen bf1 bf2),
    (lt_unpackedbf mlen elen bf1 bf2))

(** val gt_unpackedbf :
    int -> int -> unpackedbf -> unpackedbf -> QFBV.QFBV.bexp **)

let gt_unpackedbf mlen elen bf1 bf2 =
  lt_unpackedbf mlen elen bf2 bf1

(** val ge_unpackedbf :
    int -> int -> unpackedbf -> unpackedbf -> QFBV.QFBV.bexp **)

let ge_unpackedbf mlen elen bf1 bf2 =
  le_unpackedbf mlen elen bf2 bf1

(** val max_unpackedbf :
    int -> int -> (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list ->
    TypEnv.SSATE.env -> unpackedbf -> unpackedbf ->
    ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf **)

let max_unpackedbf mlen elen gen_var g es te bf1 bf2 =
  let returnRight = QFBV.QFBV.Bdisj ((isNaN_unpackedbf mlen elen bf1),
    (lt_unpackedbf mlen elen bf1 bf2))
  in
  let inf_flag0 = coq_Eite_bexp returnRight bf2.inf_flag bf1.inf_flag in
  let zero_flag0 = coq_Eite_bexp returnRight bf2.zero_flag bf1.zero_flag in
  let nan_flag0 = coq_Eite_bexp returnRight bf2.nan_flag bf1.nan_flag in
  let un_s0 = coq_Eite_bexp returnRight bf2.un_s bf1.un_s in
  let un_e0 = QFBV.QFBV.Eite (returnRight, bf2.un_e, bf1.un_e) in
  let un_m0 = QFBV.QFBV.Eite (returnRight, bf2.un_m, bf1.un_m) in
  let (p, un_e1) = make_exp_var gen_var g es te un_e0 (unpack_elen mlen elen)
  in
  let (p0, es0) = p in
  let (te0, g0) = p0 in
  let (p1, un_m1) = make_exp_var gen_var g0 es0 te0 un_m0 (unpack_mlen mlen)
  in
  let result = { inf_flag = inf_flag0; zero_flag = zero_flag0; nan_flag =
    nan_flag0; un_s = un_s0; un_e = un_e1; un_m = un_m1 }
  in
  (p1, result)

(** val min_unpackedbf :
    int -> int -> (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list ->
    TypEnv.SSATE.env -> unpackedbf -> unpackedbf ->
    ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf **)

let min_unpackedbf mlen elen gen_var g es te bf1 bf2 =
  let returnLeft = QFBV.QFBV.Bdisj ((isNaN_unpackedbf mlen elen bf2),
    (lt_unpackedbf mlen elen bf1 bf2))
  in
  let inf_flag0 = coq_Eite_bexp returnLeft bf1.inf_flag bf2.inf_flag in
  let zero_flag0 = coq_Eite_bexp returnLeft bf1.zero_flag bf2.zero_flag in
  let nan_flag0 = coq_Eite_bexp returnLeft bf1.nan_flag bf2.nan_flag in
  let un_s0 = coq_Eite_bexp returnLeft bf1.un_s bf2.un_s in
  let un_e0 = QFBV.QFBV.Eite (returnLeft, bf1.un_e, bf2.un_e) in
  let un_m0 = QFBV.QFBV.Eite (returnLeft, bf1.un_m, bf2.un_m) in
  let (p, un_e1) = make_exp_var gen_var g es te un_e0 (unpack_elen mlen elen)
  in
  let (p0, es0) = p in
  let (te0, g0) = p0 in
  let (p1, un_m1) = make_exp_var gen_var g0 es0 te0 un_m0 (unpack_mlen mlen)
  in
  let result = { inf_flag = inf_flag0; zero_flag = zero_flag0; nan_flag =
    nan_flag0; un_s = un_s0; un_e = un_e1; un_m = un_m1 }
  in
  (p1, result)
