open AdhereConform
open State
open WBPacking
open Eqtype
open Ssrnat

module MakeFq2bvq =
 struct
  type feunop =
  | FUabs
  | FUneg

  (** val feunop_rect : 'a1 -> 'a1 -> feunop -> 'a1 **)

  let feunop_rect f f0 = function
  | FUabs -> f
  | FUneg -> f0

  (** val feunop_rec : 'a1 -> 'a1 -> feunop -> 'a1 **)

  let feunop_rec f f0 = function
  | FUabs -> f
  | FUneg -> f0

  type fermunop =
  | FRUsqrt
  | FRUrti

  (** val fermunop_rect : 'a1 -> 'a1 -> fermunop -> 'a1 **)

  let fermunop_rect f f0 = function
  | FRUsqrt -> f
  | FRUrti -> f0

  (** val fermunop_rec : 'a1 -> 'a1 -> fermunop -> 'a1 **)

  let fermunop_rec f f0 = function
  | FRUsqrt -> f
  | FRUrti -> f0

  type febinop =
  | FBmax
  | FBmin
  | FBrem

  (** val febinop_rect : 'a1 -> 'a1 -> 'a1 -> febinop -> 'a1 **)

  let febinop_rect f f0 f1 = function
  | FBmax -> f
  | FBmin -> f0
  | FBrem -> f1

  (** val febinop_rec : 'a1 -> 'a1 -> 'a1 -> febinop -> 'a1 **)

  let febinop_rec f f0 f1 = function
  | FBmax -> f
  | FBmin -> f0
  | FBrem -> f1

  type fermbinop =
  | FRBadd
  | FRBsub
  | FRBmul
  | FRBdiv

  (** val fermbinop_rect : 'a1 -> 'a1 -> 'a1 -> 'a1 -> fermbinop -> 'a1 **)

  let fermbinop_rect f f0 f1 f2 = function
  | FRBadd -> f
  | FRBsub -> f0
  | FRBmul -> f1
  | FRBdiv -> f2

  (** val fermbinop_rec : 'a1 -> 'a1 -> 'a1 -> 'a1 -> fermbinop -> 'a1 **)

  let fermbinop_rec f f0 f1 f2 = function
  | FRBadd -> f
  | FRBsub -> f0
  | FRBmul -> f1
  | FRBdiv -> f2

  type fermtriop =
  | FRTfma

  (** val fermtriop_rect : 'a1 -> fermtriop -> 'a1 **)

  let fermtriop_rect f _ =
    f

  (** val fermtriop_rec : 'a1 -> fermtriop -> 'a1 **)

  let fermtriop_rec f _ =
    f

  type fbunop =
  | FUisInfinite
  | FUisZero
  | FUisNaN
  | FUisNormal
  | FUisSubnormal
  | FUisNegative
  | FUisPositive

  (** val fbunop_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> fbunop -> 'a1 **)

  let fbunop_rect f f0 f1 f2 f3 f4 f5 = function
  | FUisInfinite -> f
  | FUisZero -> f0
  | FUisNaN -> f1
  | FUisNormal -> f2
  | FUisSubnormal -> f3
  | FUisNegative -> f4
  | FUisPositive -> f5

  (** val fbunop_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> fbunop -> 'a1 **)

  let fbunop_rec f f0 f1 f2 f3 f4 f5 = function
  | FUisInfinite -> f
  | FUisZero -> f0
  | FUisNaN -> f1
  | FUisNormal -> f2
  | FUisSubnormal -> f3
  | FUisNegative -> f4
  | FUisPositive -> f5

  type fbbinop =
  | FBeq
  | FBlt
  | FBgt
  | FBleq
  | FBgeq

  (** val fbbinop_rect : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> fbbinop -> 'a1 **)

  let fbbinop_rect f f0 f1 f2 f3 = function
  | FBeq -> f
  | FBlt -> f0
  | FBgt -> f1
  | FBleq -> f2
  | FBgeq -> f3

  (** val fbbinop_rec : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> fbbinop -> 'a1 **)

  let fbbinop_rec f f0 f1 f2 f3 = function
  | FBeq -> f
  | FBlt -> f0
  | FBgt -> f1
  | FBleq -> f2
  | FBgeq -> f3

  type fp_exp =
  | FEieee754 of int * int * QFBV.QFBV.exp * QFBV.QFBV.exp * QFBV.QFBV.exp
  | FEunop of feunop * fp_exp
  | FErmunop of fermunop * QFBV.QFBV.exp * fp_exp
  | FEbinop of febinop * fp_exp * fp_exp
  | FErmbinop of fermbinop * QFBV.QFBV.exp * fp_exp * fp_exp
  | FErmtriop of fermtriop * QFBV.QFBV.exp * fp_exp * fp_exp * fp_exp
  | FEofbf of QFBV.QFBV.exp * fp_exp * int * int
  | FEofbv of QFBV.QFBV.exp * int * int * int
  | FEofsbv of QFBV.QFBV.exp * QFBV.QFBV.exp * int * int * int
  | FEofubv of QFBV.QFBV.exp * QFBV.QFBV.exp * int * int * int
  | FEite of fp_bexp * fp_exp * fp_exp
  and fp_bexp =
  | FBfalse
  | FBtrue
  | FBvar of QFBV.QFBV.exp
  | FBbveq of fp_exp * fp_exp
  | FBunop of fbunop * fp_exp
  | FBbinop of fbbinop * fp_exp * fp_exp
  | FBlneg of fp_bexp
  | FBconj of fp_bexp * fp_bexp
  | FBdisj of fp_bexp * fp_bexp

  (** val fp_exp_rect :
      (int -> int -> QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.exp -> 'a1)
      -> (feunop -> fp_exp -> 'a1 -> 'a1) -> (fermunop -> QFBV.QFBV.exp ->
      fp_exp -> 'a1 -> 'a1) -> (febinop -> fp_exp -> 'a1 -> fp_exp -> 'a1 ->
      'a1) -> (fermbinop -> QFBV.QFBV.exp -> fp_exp -> 'a1 -> fp_exp -> 'a1
      -> 'a1) -> (fermtriop -> QFBV.QFBV.exp -> fp_exp -> 'a1 -> fp_exp ->
      'a1 -> fp_exp -> 'a1 -> 'a1) -> (QFBV.QFBV.exp -> fp_exp -> 'a1 -> int
      -> int -> 'a1) -> (QFBV.QFBV.exp -> int -> int -> int -> 'a1) ->
      (QFBV.QFBV.exp -> QFBV.QFBV.exp -> int -> int -> int -> 'a1) ->
      (QFBV.QFBV.exp -> QFBV.QFBV.exp -> int -> int -> int -> 'a1) ->
      (fp_bexp -> fp_exp -> 'a1 -> fp_exp -> 'a1 -> 'a1) -> fp_exp -> 'a1 **)

  let rec fp_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 = function
  | FEieee754 (n, n0, e, e0, e1) -> f n n0 e e0 e1
  | FEunop (f11, f12) ->
    f0 f11 f12 (fp_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f12)
  | FErmunop (f11, e, f12) ->
    f1 f11 e f12 (fp_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f12)
  | FEbinop (f11, f12, f13) ->
    f2 f11 f12 (fp_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f12) f13
      (fp_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f13)
  | FErmbinop (f11, e, f12, f13) ->
    f3 f11 e f12 (fp_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f12) f13
      (fp_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f13)
  | FErmtriop (f11, e, f12, f13, f14) ->
    f4 f11 e f12 (fp_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f12) f13
      (fp_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f13) f14
      (fp_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f14)
  | FEofbf (e, f11, n, n0) ->
    f5 e f11 (fp_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f11) n n0
  | FEofbv (e, n, n0, n1) -> f6 e n n0 n1
  | FEofsbv (e, e0, n, n0, n1) -> f7 e e0 n n0 n1
  | FEofubv (e, e0, n, n0, n1) -> f8 e e0 n n0 n1
  | FEite (f11, f12, f13) ->
    f9 f11 f12 (fp_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f12) f13
      (fp_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f13)

  (** val fp_exp_rec :
      (int -> int -> QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.exp -> 'a1)
      -> (feunop -> fp_exp -> 'a1 -> 'a1) -> (fermunop -> QFBV.QFBV.exp ->
      fp_exp -> 'a1 -> 'a1) -> (febinop -> fp_exp -> 'a1 -> fp_exp -> 'a1 ->
      'a1) -> (fermbinop -> QFBV.QFBV.exp -> fp_exp -> 'a1 -> fp_exp -> 'a1
      -> 'a1) -> (fermtriop -> QFBV.QFBV.exp -> fp_exp -> 'a1 -> fp_exp ->
      'a1 -> fp_exp -> 'a1 -> 'a1) -> (QFBV.QFBV.exp -> fp_exp -> 'a1 -> int
      -> int -> 'a1) -> (QFBV.QFBV.exp -> int -> int -> int -> 'a1) ->
      (QFBV.QFBV.exp -> QFBV.QFBV.exp -> int -> int -> int -> 'a1) ->
      (QFBV.QFBV.exp -> QFBV.QFBV.exp -> int -> int -> int -> 'a1) ->
      (fp_bexp -> fp_exp -> 'a1 -> fp_exp -> 'a1 -> 'a1) -> fp_exp -> 'a1 **)

  let rec fp_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 = function
  | FEieee754 (n, n0, e, e0, e1) -> f n n0 e e0 e1
  | FEunop (f11, f12) ->
    f0 f11 f12 (fp_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f12)
  | FErmunop (f11, e, f12) ->
    f1 f11 e f12 (fp_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f12)
  | FEbinop (f11, f12, f13) ->
    f2 f11 f12 (fp_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f12) f13
      (fp_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f13)
  | FErmbinop (f11, e, f12, f13) ->
    f3 f11 e f12 (fp_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f12) f13
      (fp_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f13)
  | FErmtriop (f11, e, f12, f13, f14) ->
    f4 f11 e f12 (fp_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f12) f13
      (fp_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f13) f14
      (fp_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f14)
  | FEofbf (e, f11, n, n0) ->
    f5 e f11 (fp_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f11) n n0
  | FEofbv (e, n, n0, n1) -> f6 e n n0 n1
  | FEofsbv (e, e0, n, n0, n1) -> f7 e e0 n n0 n1
  | FEofubv (e, e0, n, n0, n1) -> f8 e e0 n n0 n1
  | FEite (f11, f12, f13) ->
    f9 f11 f12 (fp_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f12) f13
      (fp_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f13)

  (** val fp_bexp_rect :
      'a1 -> 'a1 -> (QFBV.QFBV.exp -> 'a1) -> (fp_exp -> fp_exp -> 'a1) ->
      (fbunop -> fp_exp -> 'a1) -> (fbbinop -> fp_exp -> fp_exp -> 'a1) ->
      (fp_bexp -> 'a1 -> 'a1) -> (fp_bexp -> 'a1 -> fp_bexp -> 'a1 -> 'a1) ->
      (fp_bexp -> 'a1 -> fp_bexp -> 'a1 -> 'a1) -> fp_bexp -> 'a1 **)

  let rec fp_bexp_rect f f0 f1 f2 f3 f4 f5 f6 f7 = function
  | FBfalse -> f
  | FBtrue -> f0
  | FBvar e -> f1 e
  | FBbveq (f9, f10) -> f2 f9 f10
  | FBunop (f9, f10) -> f3 f9 f10
  | FBbinop (f9, f10, f11) -> f4 f9 f10 f11
  | FBlneg f9 -> f5 f9 (fp_bexp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f9)
  | FBconj (f9, f10) ->
    f6 f9 (fp_bexp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f9) f10
      (fp_bexp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f10)
  | FBdisj (f9, f10) ->
    f7 f9 (fp_bexp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f9) f10
      (fp_bexp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f10)

  (** val fp_bexp_rec :
      'a1 -> 'a1 -> (QFBV.QFBV.exp -> 'a1) -> (fp_exp -> fp_exp -> 'a1) ->
      (fbunop -> fp_exp -> 'a1) -> (fbbinop -> fp_exp -> fp_exp -> 'a1) ->
      (fp_bexp -> 'a1 -> 'a1) -> (fp_bexp -> 'a1 -> fp_bexp -> 'a1 -> 'a1) ->
      (fp_bexp -> 'a1 -> fp_bexp -> 'a1 -> 'a1) -> fp_bexp -> 'a1 **)

  let rec fp_bexp_rec f f0 f1 f2 f3 f4 f5 f6 f7 = function
  | FBfalse -> f
  | FBtrue -> f0
  | FBvar e -> f1 e
  | FBbveq (f9, f10) -> f2 f9 f10
  | FBunop (f9, f10) -> f3 f9 f10
  | FBbinop (f9, f10, f11) -> f4 f9 f10 f11
  | FBlneg f9 -> f5 f9 (fp_bexp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f9)
  | FBconj (f9, f10) ->
    f6 f9 (fp_bexp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f9) f10
      (fp_bexp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f10)
  | FBdisj (f9, f10) ->
    f7 f9 (fp_bexp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f9) f10
      (fp_bexp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f10)

  (** val fp_exp_format : fp_exp -> int * int **)

  let rec fp_exp_format = function
  | FEieee754 (elen, mlen, _, _, _) -> (elen, mlen)
  | FEunop (_, fe0) -> fp_exp_format fe0
  | FErmunop (_, _, fe0) -> fp_exp_format fe0
  | FEbinop (_, fe1, _) -> fp_exp_format fe1
  | FErmbinop (_, _, fe1, _) -> fp_exp_format fe1
  | FErmtriop (_, _, fe1, _, _) -> fp_exp_format fe1
  | FEofbf (_, _, telen, tmlen) -> (telen, tmlen)
  | FEofbv (_, _, telen, tmlen) -> (telen, tmlen)
  | FEofsbv (_, _, _, telen, tmlen) -> (telen, tmlen)
  | FEofubv (_, _, _, telen, tmlen) -> (telen, tmlen)
  | FEite (_, fe1, _) -> fp_exp_format fe1

  (** val well_formed_fp_exp : fp_exp -> TypEnv.SSATE.env -> bool **)

  let rec well_formed_fp_exp fe te =
    match fe with
    | FEieee754 (elen, mlen, s, e, m) ->
      (&&)
        ((&&)
          ((&&)
            ((&&)
              ((&&) (leq (Pervasives.succ (Pervasives.succ 0)) elen)
                (leq (Pervasives.succ (Pervasives.succ 0)) mlen))
              (leq elen mlen))
            (eq_op nat_eqType (Obj.magic QFBV.QFBV.exp_size s te)
              (Obj.magic (Pervasives.succ 0))))
          (eq_op nat_eqType (Obj.magic QFBV.QFBV.exp_size e te)
            (Obj.magic elen)))
        (eq_op nat_eqType (Obj.magic QFBV.QFBV.exp_size m te)
          (Obj.magic mlen))
    | FEunop (_, fe0) -> well_formed_fp_exp fe0 te
    | FErmunop (_, rm, fe0) ->
      (&&)
        ((&&)
          (eq_op nat_eqType (Obj.magic QFBV.QFBV.exp_size rm te)
            (Obj.magic (Pervasives.succ (Pervasives.succ (Pervasives.succ
              0))))) (well_formed_fp_exp fe0 te))
        (eq_op nat_eqType (Obj.magic QFBV.QFBV.exp_size rm te)
          (Obj.magic (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))
    | FEbinop (_, fe1, fe2) ->
      let (elen1, mlen1) = fp_exp_format fe1 in
      let (elen2, mlen2) = fp_exp_format fe2 in
      (&&)
        ((&&)
          ((&&)
            ((&&)
              ((&&)
                ((&&) (well_formed_fp_exp fe1 te) (well_formed_fp_exp fe2 te))
                (leq (Pervasives.succ (Pervasives.succ 0)) elen1))
              (leq (Pervasives.succ (Pervasives.succ 0)) mlen1))
            (leq elen1 mlen1))
          (eq_op nat_eqType (Obj.magic elen1) (Obj.magic elen2)))
        (eq_op nat_eqType (Obj.magic mlen1) (Obj.magic mlen2))
    | FErmbinop (_, rm, fe1, fe2) ->
      let (elen1, mlen1) = fp_exp_format fe1 in
      let (elen2, mlen2) = fp_exp_format fe2 in
      (&&)
        ((&&)
          ((&&)
            ((&&)
              ((&&)
                ((&&)
                  ((&&)
                    ((&&)
                      (eq_op nat_eqType (Obj.magic QFBV.QFBV.exp_size rm te)
                        (Obj.magic (Pervasives.succ (Pervasives.succ
                          (Pervasives.succ 0))))) (well_formed_fp_exp fe1 te))
                    (well_formed_fp_exp fe2 te))
                  (leq (Pervasives.succ (Pervasives.succ 0)) elen1))
                (leq (Pervasives.succ (Pervasives.succ 0)) mlen1))
              (leq elen1 mlen1))
            (eq_op nat_eqType (Obj.magic elen1) (Obj.magic elen2)))
          (eq_op nat_eqType (Obj.magic mlen1) (Obj.magic mlen2)))
        (eq_op nat_eqType (Obj.magic QFBV.QFBV.exp_size rm te)
          (Obj.magic (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))
    | FErmtriop (_, rm, fe1, fe2, fe3) ->
      let (elen1, mlen1) = fp_exp_format fe1 in
      let (elen2, mlen2) = fp_exp_format fe2 in
      let (elen3, mlen3) = fp_exp_format fe3 in
      (&&)
        ((&&)
          ((&&)
            ((&&)
              ((&&)
                ((&&)
                  ((&&)
                    ((&&)
                      ((&&)
                        ((&&)
                          ((&&)
                            (eq_op nat_eqType
                              (Obj.magic QFBV.QFBV.exp_size rm te)
                              (Obj.magic (Pervasives.succ (Pervasives.succ
                                (Pervasives.succ 0)))))
                            (well_formed_fp_exp fe1 te))
                          (well_formed_fp_exp fe2 te))
                        (well_formed_fp_exp fe3 te))
                      (leq (Pervasives.succ (Pervasives.succ 0)) elen1))
                    (leq (Pervasives.succ (Pervasives.succ 0)) mlen1))
                  (leq elen1 mlen1))
                (eq_op nat_eqType (Obj.magic elen1) (Obj.magic elen2)))
              (eq_op nat_eqType (Obj.magic mlen1) (Obj.magic mlen2)))
            (eq_op nat_eqType (Obj.magic elen1) (Obj.magic elen3)))
          (eq_op nat_eqType (Obj.magic mlen1) (Obj.magic mlen3)))
        (eq_op nat_eqType (Obj.magic QFBV.QFBV.exp_size rm te)
          (Obj.magic (Pervasives.succ (Pervasives.succ (Pervasives.succ 0)))))
    | FEofbf (rm, fe0, telen, tmlen) ->
      let (elen, mlen) = fp_exp_format fe0 in
      (&&)
        ((&&)
          ((&&)
            ((&&)
              ((&&)
                ((&&)
                  ((&&)
                    (eq_op nat_eqType (Obj.magic QFBV.QFBV.exp_size rm te)
                      (Obj.magic (Pervasives.succ (Pervasives.succ
                        (Pervasives.succ 0))))) (well_formed_fp_exp fe0 te))
                  (leq (Pervasives.succ (Pervasives.succ 0)) elen))
                (leq (Pervasives.succ (Pervasives.succ 0)) mlen))
              (leq elen mlen))
            (leq (Pervasives.succ (Pervasives.succ 0)) telen))
          (leq (Pervasives.succ (Pervasives.succ 0)) tmlen)) (leq telen tmlen)
    | FEofbv (e, n, telen, tmlen) ->
      (&&)
        ((&&)
          ((&&)
            ((&&) (leq (Pervasives.succ (Pervasives.succ 0)) telen)
              (leq (Pervasives.succ (Pervasives.succ 0)) tmlen))
            (leq telen tmlen))
          (eq_op nat_eqType (Obj.magic n)
            (Obj.magic addn (addn telen tmlen) (Pervasives.succ 0))))
        (eq_op nat_eqType (Obj.magic QFBV.QFBV.exp_size e te) (Obj.magic n))
    | FEofsbv (rm, e, n, telen, tmlen) ->
      (&&)
        ((&&)
          ((&&)
            ((&&)
              ((&&)
                (eq_op nat_eqType (Obj.magic QFBV.QFBV.exp_size rm te)
                  (Obj.magic (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ 0)))))
                (leq (Pervasives.succ (Pervasives.succ 0)) n))
              (eq_op nat_eqType (Obj.magic QFBV.QFBV.exp_size e te)
                (Obj.magic n)))
            (leq (Pervasives.succ (Pervasives.succ 0)) telen))
          (leq (Pervasives.succ (Pervasives.succ 0)) tmlen)) (leq telen tmlen)
    | FEofubv (rm, e, n, telen, tmlen) ->
      (&&)
        ((&&)
          ((&&)
            ((&&)
              ((&&)
                (eq_op nat_eqType (Obj.magic QFBV.QFBV.exp_size rm te)
                  (Obj.magic (Pervasives.succ (Pervasives.succ
                    (Pervasives.succ 0)))))
                (leq (Pervasives.succ (Pervasives.succ 0)) n))
              (eq_op nat_eqType (Obj.magic QFBV.QFBV.exp_size e te)
                (Obj.magic n)))
            (leq (Pervasives.succ (Pervasives.succ 0)) telen))
          (leq (Pervasives.succ (Pervasives.succ 0)) tmlen)) (leq telen tmlen)
    | FEite (fb, fe1, fe2) ->
      let (elen1, mlen1) = fp_exp_format fe1 in
      let (elen2, mlen2) = fp_exp_format fe2 in
      (&&)
        ((&&)
          ((&&)
            ((&&)
              ((&&)
                ((&&)
                  ((&&) (well_formed_fp_bexp fb te)
                    (well_formed_fp_exp fe1 te)) (well_formed_fp_exp fe2 te))
                (leq (Pervasives.succ (Pervasives.succ 0)) elen1))
              (leq (Pervasives.succ (Pervasives.succ 0)) mlen1))
            (leq elen1 mlen1))
          (eq_op nat_eqType (Obj.magic elen1) (Obj.magic elen2)))
        (eq_op nat_eqType (Obj.magic mlen1) (Obj.magic mlen2))

  (** val well_formed_fp_bexp : fp_bexp -> TypEnv.SSATE.env -> bool **)

  and well_formed_fp_bexp fb te =
    match fb with
    | FBvar v ->
      eq_op nat_eqType (Obj.magic QFBV.QFBV.exp_size v te)
        (Obj.magic (Pervasives.succ 0))
    | FBbveq (fe1, fe2) ->
      let (elen1, mlen1) = fp_exp_format fe1 in
      let (elen2, mlen2) = fp_exp_format fe2 in
      (&&)
        ((&&)
          ((&&)
            ((&&)
              ((&&)
                ((&&) (well_formed_fp_exp fe1 te) (well_formed_fp_exp fe2 te))
                (leq (Pervasives.succ (Pervasives.succ 0)) elen1))
              (leq (Pervasives.succ (Pervasives.succ 0)) mlen1))
            (leq elen1 mlen1))
          (eq_op nat_eqType (Obj.magic elen1) (Obj.magic elen2)))
        (eq_op nat_eqType (Obj.magic mlen1) (Obj.magic mlen2))
    | FBunop (_, fe) -> well_formed_fp_exp fe te
    | FBbinop (_, fe1, fe2) ->
      let (elen1, mlen1) = fp_exp_format fe1 in
      let (elen2, mlen2) = fp_exp_format fe2 in
      (&&)
        ((&&)
          ((&&)
            ((&&)
              ((&&)
                ((&&) (well_formed_fp_exp fe1 te) (well_formed_fp_exp fe2 te))
                (leq (Pervasives.succ (Pervasives.succ 0)) elen1))
              (leq (Pervasives.succ (Pervasives.succ 0)) mlen1))
            (leq elen1 mlen1))
          (eq_op nat_eqType (Obj.magic elen1) (Obj.magic elen2)))
        (eq_op nat_eqType (Obj.magic mlen1) (Obj.magic mlen2))
    | FBlneg fb0 -> well_formed_fp_bexp fb0 te
    | FBconj (fb1, fb2) ->
      (&&) (well_formed_fp_bexp fb1 te) (well_formed_fp_bexp fb2 te)
    | FBdisj (fb1, fb2) ->
      (&&) (well_formed_fp_bexp fb1 te) (well_formed_fp_bexp fb2 te)
    | _ -> true

  (** val well_formed_fp_bexps : fp_bexp list -> TypEnv.SSATE.env -> bool **)

  let rec well_formed_fp_bexps bs te =
    match bs with
    | [] -> true
    | b :: bs' ->
      (&&) (well_formed_fp_bexp b te) (well_formed_fp_bexps bs' te)

  (** val well_formed_unpackedbf : unpackedbf -> TypEnv.SSATE.env -> bool **)

  let well_formed_unpackedbf ubf te =
    (&&)
      ((&&)
        ((&&)
          ((&&)
            ((&&) (QFBV.QFBV.well_formed_bexp ubf.inf_flag te)
              (QFBV.QFBV.well_formed_bexp ubf.zero_flag te))
            (QFBV.QFBV.well_formed_bexp ubf.nan_flag te))
          (QFBV.QFBV.well_formed_bexp ubf.un_s te))
        (QFBV.QFBV.well_formed_exp ubf.un_e te))
      (QFBV.QFBV.well_formed_exp ubf.un_m te)

  (** val conform_unpackedbf :
      unpackedbf -> SSAStore.t -> TypEnv.SSATE.env -> bool **)

  let conform_unpackedbf ubf s te =
    (&&)
      ((&&)
        ((&&)
          ((&&)
            ((&&) (conform_bexp ubf.inf_flag s te)
              (conform_bexp ubf.zero_flag s te))
            (conform_bexp ubf.nan_flag s te)) (conform_bexp ubf.un_s s te))
        (conform_exp ubf.un_e s te)) (conform_exp ubf.un_m s te)
 end

module Fq2bvq = MakeFq2bvq
