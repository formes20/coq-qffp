open AdhereConform
open State
open WBPacking
open Eqtype
open Ssrnat

module MakeFq2bvq :
 sig
  type feunop =
  | FUabs
  | FUneg

  val feunop_rect : 'a1 -> 'a1 -> feunop -> 'a1

  val feunop_rec : 'a1 -> 'a1 -> feunop -> 'a1

  type fermunop =
  | FRUsqrt
  | FRUrti

  val fermunop_rect : 'a1 -> 'a1 -> fermunop -> 'a1

  val fermunop_rec : 'a1 -> 'a1 -> fermunop -> 'a1

  type febinop =
  | FBmax
  | FBmin
  | FBrem

  val febinop_rect : 'a1 -> 'a1 -> 'a1 -> febinop -> 'a1

  val febinop_rec : 'a1 -> 'a1 -> 'a1 -> febinop -> 'a1

  type fermbinop =
  | FRBadd
  | FRBsub
  | FRBmul
  | FRBdiv

  val fermbinop_rect : 'a1 -> 'a1 -> 'a1 -> 'a1 -> fermbinop -> 'a1

  val fermbinop_rec : 'a1 -> 'a1 -> 'a1 -> 'a1 -> fermbinop -> 'a1

  type fermtriop =
  | FRTfma

  val fermtriop_rect : 'a1 -> fermtriop -> 'a1

  val fermtriop_rec : 'a1 -> fermtriop -> 'a1

  type fbunop =
  | FUisInfinite
  | FUisZero
  | FUisNaN
  | FUisNormal
  | FUisSubnormal
  | FUisNegative
  | FUisPositive

  val fbunop_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> fbunop -> 'a1

  val fbunop_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> fbunop -> 'a1

  type fbbinop =
  | FBeq
  | FBlt
  | FBgt
  | FBleq
  | FBgeq

  val fbbinop_rect : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> fbbinop -> 'a1

  val fbbinop_rec : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> fbbinop -> 'a1

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

  val fp_exp_rect :
    (int -> int -> QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.exp -> 'a1) ->
    (feunop -> fp_exp -> 'a1 -> 'a1) -> (fermunop -> QFBV.QFBV.exp -> fp_exp
    -> 'a1 -> 'a1) -> (febinop -> fp_exp -> 'a1 -> fp_exp -> 'a1 -> 'a1) ->
    (fermbinop -> QFBV.QFBV.exp -> fp_exp -> 'a1 -> fp_exp -> 'a1 -> 'a1) ->
    (fermtriop -> QFBV.QFBV.exp -> fp_exp -> 'a1 -> fp_exp -> 'a1 -> fp_exp
    -> 'a1 -> 'a1) -> (QFBV.QFBV.exp -> fp_exp -> 'a1 -> int -> int -> 'a1)
    -> (QFBV.QFBV.exp -> int -> int -> int -> 'a1) -> (QFBV.QFBV.exp ->
    QFBV.QFBV.exp -> int -> int -> int -> 'a1) -> (QFBV.QFBV.exp ->
    QFBV.QFBV.exp -> int -> int -> int -> 'a1) -> (fp_bexp -> fp_exp -> 'a1
    -> fp_exp -> 'a1 -> 'a1) -> fp_exp -> 'a1

  val fp_exp_rec :
    (int -> int -> QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.exp -> 'a1) ->
    (feunop -> fp_exp -> 'a1 -> 'a1) -> (fermunop -> QFBV.QFBV.exp -> fp_exp
    -> 'a1 -> 'a1) -> (febinop -> fp_exp -> 'a1 -> fp_exp -> 'a1 -> 'a1) ->
    (fermbinop -> QFBV.QFBV.exp -> fp_exp -> 'a1 -> fp_exp -> 'a1 -> 'a1) ->
    (fermtriop -> QFBV.QFBV.exp -> fp_exp -> 'a1 -> fp_exp -> 'a1 -> fp_exp
    -> 'a1 -> 'a1) -> (QFBV.QFBV.exp -> fp_exp -> 'a1 -> int -> int -> 'a1)
    -> (QFBV.QFBV.exp -> int -> int -> int -> 'a1) -> (QFBV.QFBV.exp ->
    QFBV.QFBV.exp -> int -> int -> int -> 'a1) -> (QFBV.QFBV.exp ->
    QFBV.QFBV.exp -> int -> int -> int -> 'a1) -> (fp_bexp -> fp_exp -> 'a1
    -> fp_exp -> 'a1 -> 'a1) -> fp_exp -> 'a1

  val fp_bexp_rect :
    'a1 -> 'a1 -> (QFBV.QFBV.exp -> 'a1) -> (fp_exp -> fp_exp -> 'a1) ->
    (fbunop -> fp_exp -> 'a1) -> (fbbinop -> fp_exp -> fp_exp -> 'a1) ->
    (fp_bexp -> 'a1 -> 'a1) -> (fp_bexp -> 'a1 -> fp_bexp -> 'a1 -> 'a1) ->
    (fp_bexp -> 'a1 -> fp_bexp -> 'a1 -> 'a1) -> fp_bexp -> 'a1

  val fp_bexp_rec :
    'a1 -> 'a1 -> (QFBV.QFBV.exp -> 'a1) -> (fp_exp -> fp_exp -> 'a1) ->
    (fbunop -> fp_exp -> 'a1) -> (fbbinop -> fp_exp -> fp_exp -> 'a1) ->
    (fp_bexp -> 'a1 -> 'a1) -> (fp_bexp -> 'a1 -> fp_bexp -> 'a1 -> 'a1) ->
    (fp_bexp -> 'a1 -> fp_bexp -> 'a1 -> 'a1) -> fp_bexp -> 'a1

  val fp_exp_format : fp_exp -> int * int

  val well_formed_fp_exp : fp_exp -> TypEnv.SSATE.env -> bool

  val well_formed_fp_bexp : fp_bexp -> TypEnv.SSATE.env -> bool

  val well_formed_fp_bexps : fp_bexp list -> TypEnv.SSATE.env -> bool

  val well_formed_unpackedbf : unpackedbf -> TypEnv.SSATE.env -> bool

  val conform_unpackedbf :
    unpackedbf -> SSAStore.t -> TypEnv.SSATE.env -> bool
 end

module Fq2bvq :
 sig
  type feunop = MakeFq2bvq.feunop =
  | FUabs
  | FUneg

  val feunop_rect : 'a1 -> 'a1 -> feunop -> 'a1

  val feunop_rec : 'a1 -> 'a1 -> feunop -> 'a1

  type fermunop = MakeFq2bvq.fermunop =
  | FRUsqrt
  | FRUrti

  val fermunop_rect : 'a1 -> 'a1 -> fermunop -> 'a1

  val fermunop_rec : 'a1 -> 'a1 -> fermunop -> 'a1

  type febinop = MakeFq2bvq.febinop =
  | FBmax
  | FBmin
  | FBrem

  val febinop_rect : 'a1 -> 'a1 -> 'a1 -> febinop -> 'a1

  val febinop_rec : 'a1 -> 'a1 -> 'a1 -> febinop -> 'a1

  type fermbinop = MakeFq2bvq.fermbinop =
  | FRBadd
  | FRBsub
  | FRBmul
  | FRBdiv

  val fermbinop_rect : 'a1 -> 'a1 -> 'a1 -> 'a1 -> fermbinop -> 'a1

  val fermbinop_rec : 'a1 -> 'a1 -> 'a1 -> 'a1 -> fermbinop -> 'a1

  type fermtriop = MakeFq2bvq.fermtriop =
  | FRTfma

  val fermtriop_rect : 'a1 -> fermtriop -> 'a1

  val fermtriop_rec : 'a1 -> fermtriop -> 'a1

  type fbunop = MakeFq2bvq.fbunop =
  | FUisInfinite
  | FUisZero
  | FUisNaN
  | FUisNormal
  | FUisSubnormal
  | FUisNegative
  | FUisPositive

  val fbunop_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> fbunop -> 'a1

  val fbunop_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> fbunop -> 'a1

  type fbbinop = MakeFq2bvq.fbbinop =
  | FBeq
  | FBlt
  | FBgt
  | FBleq
  | FBgeq

  val fbbinop_rect : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> fbbinop -> 'a1

  val fbbinop_rec : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> fbbinop -> 'a1

  type fp_exp = MakeFq2bvq.fp_exp =
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
  and fp_bexp = MakeFq2bvq.fp_bexp =
  | FBfalse
  | FBtrue
  | FBvar of QFBV.QFBV.exp
  | FBbveq of fp_exp * fp_exp
  | FBunop of fbunop * fp_exp
  | FBbinop of fbbinop * fp_exp * fp_exp
  | FBlneg of fp_bexp
  | FBconj of fp_bexp * fp_bexp
  | FBdisj of fp_bexp * fp_bexp

  val fp_exp_rect :
    (int -> int -> QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.exp -> 'a1) ->
    (feunop -> fp_exp -> 'a1 -> 'a1) -> (fermunop -> QFBV.QFBV.exp -> fp_exp
    -> 'a1 -> 'a1) -> (febinop -> fp_exp -> 'a1 -> fp_exp -> 'a1 -> 'a1) ->
    (fermbinop -> QFBV.QFBV.exp -> fp_exp -> 'a1 -> fp_exp -> 'a1 -> 'a1) ->
    (fermtriop -> QFBV.QFBV.exp -> fp_exp -> 'a1 -> fp_exp -> 'a1 -> fp_exp
    -> 'a1 -> 'a1) -> (QFBV.QFBV.exp -> fp_exp -> 'a1 -> int -> int -> 'a1)
    -> (QFBV.QFBV.exp -> int -> int -> int -> 'a1) -> (QFBV.QFBV.exp ->
    QFBV.QFBV.exp -> int -> int -> int -> 'a1) -> (QFBV.QFBV.exp ->
    QFBV.QFBV.exp -> int -> int -> int -> 'a1) -> (fp_bexp -> fp_exp -> 'a1
    -> fp_exp -> 'a1 -> 'a1) -> fp_exp -> 'a1

  val fp_exp_rec :
    (int -> int -> QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.exp -> 'a1) ->
    (feunop -> fp_exp -> 'a1 -> 'a1) -> (fermunop -> QFBV.QFBV.exp -> fp_exp
    -> 'a1 -> 'a1) -> (febinop -> fp_exp -> 'a1 -> fp_exp -> 'a1 -> 'a1) ->
    (fermbinop -> QFBV.QFBV.exp -> fp_exp -> 'a1 -> fp_exp -> 'a1 -> 'a1) ->
    (fermtriop -> QFBV.QFBV.exp -> fp_exp -> 'a1 -> fp_exp -> 'a1 -> fp_exp
    -> 'a1 -> 'a1) -> (QFBV.QFBV.exp -> fp_exp -> 'a1 -> int -> int -> 'a1)
    -> (QFBV.QFBV.exp -> int -> int -> int -> 'a1) -> (QFBV.QFBV.exp ->
    QFBV.QFBV.exp -> int -> int -> int -> 'a1) -> (QFBV.QFBV.exp ->
    QFBV.QFBV.exp -> int -> int -> int -> 'a1) -> (fp_bexp -> fp_exp -> 'a1
    -> fp_exp -> 'a1 -> 'a1) -> fp_exp -> 'a1

  val fp_bexp_rect :
    'a1 -> 'a1 -> (QFBV.QFBV.exp -> 'a1) -> (fp_exp -> fp_exp -> 'a1) ->
    (fbunop -> fp_exp -> 'a1) -> (fbbinop -> fp_exp -> fp_exp -> 'a1) ->
    (fp_bexp -> 'a1 -> 'a1) -> (fp_bexp -> 'a1 -> fp_bexp -> 'a1 -> 'a1) ->
    (fp_bexp -> 'a1 -> fp_bexp -> 'a1 -> 'a1) -> fp_bexp -> 'a1

  val fp_bexp_rec :
    'a1 -> 'a1 -> (QFBV.QFBV.exp -> 'a1) -> (fp_exp -> fp_exp -> 'a1) ->
    (fbunop -> fp_exp -> 'a1) -> (fbbinop -> fp_exp -> fp_exp -> 'a1) ->
    (fp_bexp -> 'a1 -> 'a1) -> (fp_bexp -> 'a1 -> fp_bexp -> 'a1 -> 'a1) ->
    (fp_bexp -> 'a1 -> fp_bexp -> 'a1 -> 'a1) -> fp_bexp -> 'a1

  val fp_exp_format : fp_exp -> int * int

  val well_formed_fp_exp : fp_exp -> TypEnv.SSATE.env -> bool

  val well_formed_fp_bexp : fp_bexp -> TypEnv.SSATE.env -> bool

  val well_formed_fp_bexps : fp_bexp list -> TypEnv.SSATE.env -> bool

  val well_formed_unpackedbf : unpackedbf -> TypEnv.SSATE.env -> bool

  val conform_unpackedbf :
    unpackedbf -> SSAStore.t -> TypEnv.SSATE.env -> bool
 end
