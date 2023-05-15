open EqVar
open WBAbsNeg
open WBAddSub
open WBClassify
open WBCommon
open WBCompare
open WBDiv
open WBFma
open WBMul
open WBOfbv
open WBOffp
open WBPacking
open WBRem
open WBRti
open WBSqrt

(** val feunop_denote :
    Fq2bvq.Fq2bvq.feunop -> int -> int -> (int -> ssavar * int) -> int ->
    QFBV.QFBV.bexp list -> TypEnv.SSATE.env -> unpackedbf ->
    ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf **)

let feunop_denote = function
| Fq2bvq.Fq2bvq.FUabs -> abs_unpackedbf
| Fq2bvq.Fq2bvq.FUneg -> neg_unpackedbf

(** val fermunop_denote :
    Fq2bvq.Fq2bvq.fermunop -> int -> int -> (int -> ssavar * int) -> int ->
    QFBV.QFBV.bexp list -> TypEnv.SSATE.env -> QFBV.QFBV.exp -> unpackedbf ->
    ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf **)

let fermunop_denote = function
| Fq2bvq.Fq2bvq.FRUsqrt -> sqrt_unpackbf
| Fq2bvq.Fq2bvq.FRUrti -> roundToIntegral_unpackbf

(** val febinop_denote :
    Fq2bvq.Fq2bvq.febinop -> int -> int -> (int -> ssavar * int) -> int ->
    QFBV.QFBV.bexp list -> TypEnv.SSATE.env -> unpackedbf -> unpackedbf ->
    ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf **)

let febinop_denote = function
| Fq2bvq.Fq2bvq.FBmax -> max_unpackedbf
| Fq2bvq.Fq2bvq.FBmin -> min_unpackedbf
| Fq2bvq.Fq2bvq.FBrem -> remrne_unpackbf

(** val fermbinop_denote :
    Fq2bvq.Fq2bvq.fermbinop -> int -> int -> (int -> ssavar * int) -> int ->
    QFBV.QFBV.bexp list -> TypEnv.SSATE.env -> QFBV.QFBV.exp -> unpackedbf ->
    unpackedbf -> ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp
    list) * unpackedbf **)

let fermbinop_denote = function
| Fq2bvq.Fq2bvq.FRBadd -> add_unpackbf
| Fq2bvq.Fq2bvq.FRBsub -> sub_unpackbf
| Fq2bvq.Fq2bvq.FRBmul -> mul_unpackbf
| Fq2bvq.Fq2bvq.FRBdiv -> div_unpackbf

(** val fermtriop_denote :
    Fq2bvq.Fq2bvq.fermtriop -> int -> int -> (int -> ssavar * int) -> int ->
    QFBV.QFBV.bexp list -> TypEnv.SSATE.env -> QFBV.QFBV.exp -> unpackedbf ->
    unpackedbf -> unpackedbf -> ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp
    list) * unpackedbf **)

let fermtriop_denote _ =
  fma_unpackbf

(** val fbunop_denote :
    Fq2bvq.Fq2bvq.fbunop -> int -> int -> unpackedbf -> QFBV.QFBV.bexp **)

let fbunop_denote = function
| Fq2bvq.Fq2bvq.FUisInfinite -> isInfinite_unpackedbf
| Fq2bvq.Fq2bvq.FUisZero -> isZero_unpackedbf
| Fq2bvq.Fq2bvq.FUisNaN -> isNaN_unpackedbf
| Fq2bvq.Fq2bvq.FUisNormal -> isNormal_unpackedbf
| Fq2bvq.Fq2bvq.FUisSubnormal -> isSubNormal_unpackedbf
| Fq2bvq.Fq2bvq.FUisNegative -> isNegative_unpackedbf
| Fq2bvq.Fq2bvq.FUisPositive -> isPositive_unpackedbf

(** val fbbinop_denote :
    Fq2bvq.Fq2bvq.fbbinop -> int -> int -> unpackedbf -> unpackedbf ->
    QFBV.QFBV.bexp **)

let fbbinop_denote = function
| Fq2bvq.Fq2bvq.FBeq -> eq_unpackedbf
| Fq2bvq.Fq2bvq.FBlt -> lt_unpackedbf
| Fq2bvq.Fq2bvq.FBgt -> gt_unpackedbf
| Fq2bvq.Fq2bvq.FBleq -> le_unpackedbf
| Fq2bvq.Fq2bvq.FBgeq -> ge_unpackedbf

(** val word_blast_exp :
    (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list -> TypEnv.SSATE.env
    -> Fq2bvq.Fq2bvq.fp_exp -> ((((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp
    list) * unpackedbf) * int) * int **)

let rec word_blast_exp gen_var g es te = function
| Fq2bvq.Fq2bvq.FEieee754 (elen, mlen, s, e, m) ->
  (((unpack mlen elen gen_var g es te s e m), elen), mlen)
| Fq2bvq.Fq2bvq.FEunop (op, fe0) ->
  let (p, mlen) = word_blast_exp gen_var g es te fe0 in
  let (p0, elen) = p in
  let (p1, ubf) = p0 in
  let (p2, es0) = p1 in
  let (te0, g0) = p2 in
  (((feunop_denote op mlen elen gen_var g0 es0 te0 ubf), elen), mlen)
| Fq2bvq.Fq2bvq.FErmunop (op, rm, fe0) ->
  let (p, mlen) = word_blast_exp gen_var g es te fe0 in
  let (p0, elen) = p in
  let (p1, ubf) = p0 in
  let (p2, es0) = p1 in
  let (te0, g0) = p2 in
  (((fermunop_denote op mlen elen gen_var g0 es0 te0 rm ubf), elen), mlen)
| Fq2bvq.Fq2bvq.FEbinop (op, fe1, fe2) ->
  let (p, mlen) = word_blast_exp gen_var g es te fe1 in
  let (p0, elen) = p in
  let (p1, ubf1) = p0 in
  let (p2, es0) = p1 in
  let (te0, g0) = p2 in
  let (p3, _) = word_blast_exp gen_var g0 es0 te0 fe2 in
  let (p4, _) = p3 in
  let (p5, ubf2) = p4 in
  let (p6, es1) = p5 in
  let (te1, g1) = p6 in
  (((febinop_denote op mlen elen gen_var g1 es1 te1 ubf1 ubf2), elen), mlen)
| Fq2bvq.Fq2bvq.FErmbinop (op, rm, fe1, fe2) ->
  let (p, mlen) = word_blast_exp gen_var g es te fe1 in
  let (p0, elen) = p in
  let (p1, ubf1) = p0 in
  let (p2, es0) = p1 in
  let (te0, g0) = p2 in
  let (p3, _) = word_blast_exp gen_var g0 es0 te0 fe2 in
  let (p4, _) = p3 in
  let (p5, ubf2) = p4 in
  let (p6, es1) = p5 in
  let (te1, g1) = p6 in
  (((fermbinop_denote op mlen elen gen_var g1 es1 te1 rm ubf1 ubf2), elen),
  mlen)
| Fq2bvq.Fq2bvq.FErmtriop (op, rm, fe1, fe2, fe3) ->
  let (p, mlen) = word_blast_exp gen_var g es te fe1 in
  let (p0, elen) = p in
  let (p1, ubf1) = p0 in
  let (p2, es0) = p1 in
  let (te0, g0) = p2 in
  let (p3, _) = word_blast_exp gen_var g0 es0 te0 fe2 in
  let (p4, _) = p3 in
  let (p5, ubf2) = p4 in
  let (p6, es1) = p5 in
  let (te1, g1) = p6 in
  let (p7, _) = word_blast_exp gen_var g1 es1 te1 fe3 in
  let (p8, _) = p7 in
  let (p9, ubf3) = p8 in
  let (p10, es2) = p9 in
  let (te2, g2) = p10 in
  (((fermtriop_denote op mlen elen gen_var g2 es2 te2 rm ubf1 ubf2 ubf3),
  elen), mlen)
| Fq2bvq.Fq2bvq.FEofbf (rm, fe0, telen, tmlen) ->
  let (p, mlen) = word_blast_exp gen_var g es te fe0 in
  let (p0, elen) = p in
  let (p1, ubf) = p0 in
  let (p2, es0) = p1 in
  let (te0, g0) = p2 in
  (((of_unpackbf gen_var g0 es0 te0 rm ubf elen mlen telen tmlen), telen),
  tmlen)
| Fq2bvq.Fq2bvq.FEofbv (e, _, telen, tmlen) ->
  (((unpack tmlen telen gen_var g es te (s_exp tmlen telen e)
      (e_exp tmlen telen e) (m_exp tmlen e)), telen), tmlen)
| Fq2bvq.Fq2bvq.FEofsbv (rm, e, n, telen, tmlen) ->
  (((of_sbv_unpackbf gen_var g es te rm e n telen tmlen), telen), tmlen)
| Fq2bvq.Fq2bvq.FEofubv (rm, e, n, telen, tmlen) ->
  (((of_ubv_unpackbf gen_var g es te rm e n telen tmlen), telen), tmlen)
| Fq2bvq.Fq2bvq.FEite (fb, fe1, fe2) ->
  let (p, be) = word_blast_bexp gen_var g es te fb in
  let (p0, es0) = p in
  let (te0, g0) = p0 in
  let (p1, mlen) = word_blast_exp gen_var g0 es0 te0 fe1 in
  let (p2, elen) = p1 in
  let (p3, ubf1) = p2 in
  let (p4, es1) = p3 in
  let (te1, g1) = p4 in
  let (p5, _) = word_blast_exp gen_var g1 es1 te1 fe2 in
  let (p6, _) = p5 in
  let (p7, ubf2) = p6 in
  let inf_flag0 = coq_Eite_bexp be ubf1.inf_flag ubf2.inf_flag in
  let zero_flag0 = coq_Eite_bexp be ubf1.zero_flag ubf2.zero_flag in
  let nan_flag0 = coq_Eite_bexp be ubf1.nan_flag ubf2.nan_flag in
  let un_s0 = coq_Eite_bexp be ubf1.un_s ubf2.un_s in
  let un_e0 = QFBV.QFBV.Eite (be, ubf1.un_e, ubf2.un_e) in
  let un_m0 = QFBV.QFBV.Eite (be, ubf1.un_m, ubf2.un_m) in
  let result = { inf_flag = inf_flag0; zero_flag = zero_flag0; nan_flag =
    nan_flag0; un_s = un_s0; un_e = un_e0; un_m = un_m0 }
  in
  (((p7, result), elen), mlen)

(** val word_blast_bexp :
    (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list -> TypEnv.SSATE.env
    -> Fq2bvq.Fq2bvq.fp_bexp -> ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp
    list) * QFBV.QFBV.bexp **)

and word_blast_bexp gen_var g es te = function
| Fq2bvq.Fq2bvq.FBfalse -> (((te, g), es), QFBV.QFBV.Bfalse)
| Fq2bvq.Fq2bvq.FBtrue -> (((te, g), es), QFBV.QFBV.Btrue)
| Fq2bvq.Fq2bvq.FBvar v ->
  (((te, g), es), (QFBV.QFBV.Bbinop (QFBV.QFBV.Beq, v, (QFBV.QFBV.Econst
    (true :: [])))))
| Fq2bvq.Fq2bvq.FBbveq (fe1, fe2) ->
  let (p, mlen) = word_blast_exp gen_var g es te fe1 in
  let (p0, elen) = p in
  let (p1, ubf1) = p0 in
  let (p2, es0) = p1 in
  let (te0, g0) = p2 in
  let (p3, _) = word_blast_exp gen_var g0 es0 te0 fe2 in
  let (p4, _) = p3 in
  let (p5, ubf2) = p4 in
  let (p6, m1) = pack mlen elen ubf1 in
  let (s1, e1) = p6 in
  let (p7, m2) = pack mlen elen ubf2 in
  let (s2, e2) = p7 in
  (p5, (QFBV.QFBV.Bconj ((QFBV.QFBV.Bconj ((QFBV.QFBV.Bbinop (QFBV.QFBV.Beq,
  s1, s2)), (QFBV.QFBV.Bbinop (QFBV.QFBV.Beq, e1, e2)))), (QFBV.QFBV.Bbinop
  (QFBV.QFBV.Beq, m1, m2)))))
| Fq2bvq.Fq2bvq.FBunop (op, fe) ->
  let (p, mlen) = word_blast_exp gen_var g es te fe in
  let (p0, elen) = p in
  let (p1, ubf) = p0 in (p1, (fbunop_denote op mlen elen ubf))
| Fq2bvq.Fq2bvq.FBbinop (op, fe1, fe2) ->
  let (p, mlen) = word_blast_exp gen_var g es te fe1 in
  let (p0, elen) = p in
  let (p1, ubf1) = p0 in
  let (p2, es0) = p1 in
  let (te0, g0) = p2 in
  let (p3, _) = word_blast_exp gen_var g0 es0 te0 fe2 in
  let (p4, _) = p3 in
  let (p5, ubf2) = p4 in (p5, (fbbinop_denote op mlen elen ubf1 ubf2))
| Fq2bvq.Fq2bvq.FBlneg fb0 ->
  let (p, fb') = word_blast_bexp gen_var g es te fb0 in
  (p, (QFBV.QFBV.Blneg fb'))
| Fq2bvq.Fq2bvq.FBconj (fb1, fb2) ->
  let (p, fb1') = word_blast_bexp gen_var g es te fb1 in
  let (p0, es0) = p in
  let (te0, g0) = p0 in
  let (p1, fb2') = word_blast_bexp gen_var g0 es0 te0 fb2 in
  (p1, (QFBV.QFBV.Bconj (fb1', fb2')))
| Fq2bvq.Fq2bvq.FBdisj (fb1, fb2) ->
  let (p, fb1') = word_blast_bexp gen_var g es te fb1 in
  let (p0, es0) = p in
  let (te0, g0) = p0 in
  let (p1, fb2') = word_blast_bexp gen_var g0 es0 te0 fb2 in
  (p1, (QFBV.QFBV.Bdisj (fb1', fb2')))

(** val word_blast_bexps :
    (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list -> TypEnv.SSATE.env
    -> Fq2bvq.Fq2bvq.fp_bexp list ->
    (TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list **)

let rec word_blast_bexps gen_var g es te = function
| [] -> ((te, g), es)
| fb :: fbs' ->
  let (p, b) = word_blast_bexp gen_var g es te fb in
  let (p0, es') = p in
  let (te', g') = p0 in word_blast_bexps gen_var g' (b :: es') te' fbs'
