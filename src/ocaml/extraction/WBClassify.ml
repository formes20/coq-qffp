open WBPacking

(** val isInfinite_unpackedbf :
    int -> int -> unpackedbf -> QFBV.QFBV.bexp **)

let isInfinite_unpackedbf _ _ bf =
  bf.inf_flag

(** val isZero_unpackedbf : int -> int -> unpackedbf -> QFBV.QFBV.bexp **)

let isZero_unpackedbf _ _ bf =
  bf.zero_flag

(** val isNaN_unpackedbf : int -> int -> unpackedbf -> QFBV.QFBV.bexp **)

let isNaN_unpackedbf _ _ bf =
  bf.nan_flag

(** val isNormal_unpackedbf : int -> int -> unpackedbf -> QFBV.QFBV.bexp **)

let isNormal_unpackedbf mlen elen bf =
  QFBV.QFBV.Bconj ((QFBV.QFBV.Bconj ((QFBV.QFBV.Bconj ((QFBV.QFBV.Blneg
    bf.inf_flag), (QFBV.QFBV.Blneg bf.zero_flag))), (QFBV.QFBV.Blneg
    bf.nan_flag))),
    (is_in_normal_range_bexp mlen elen bf.un_e (unpack_elen mlen elen)))

(** val isSubNormal_unpackedbf :
    int -> int -> unpackedbf -> QFBV.QFBV.bexp **)

let isSubNormal_unpackedbf mlen elen bf =
  QFBV.QFBV.Bconj ((QFBV.QFBV.Bconj ((QFBV.QFBV.Bconj ((QFBV.QFBV.Blneg
    bf.inf_flag), (QFBV.QFBV.Blneg bf.zero_flag))), (QFBV.QFBV.Blneg
    bf.nan_flag))),
    (is_in_subnormal_range_bexp mlen elen bf.un_e (unpack_elen mlen elen)))

(** val isPositive_unpackedbf : int -> int -> unpackedbf -> QFBV.QFBV.bexp **)

let isPositive_unpackedbf _ _ bf =
  QFBV.QFBV.Bconj ((QFBV.QFBV.Blneg bf.nan_flag), (QFBV.QFBV.Blneg bf.un_s))

(** val isNegative_unpackedbf : int -> int -> unpackedbf -> QFBV.QFBV.bexp **)

let isNegative_unpackedbf _ _ bf =
  QFBV.QFBV.Bconj ((QFBV.QFBV.Blneg bf.nan_flag), bf.un_s)

(** val isPosInfinite_unpackedbf :
    int -> int -> unpackedbf -> QFBV.QFBV.bexp **)

let isPosInfinite_unpackedbf mlen elen bf =
  QFBV.QFBV.Bconj ((isInfinite_unpackedbf mlen elen bf), (QFBV.QFBV.Blneg
    bf.un_s))

(** val isNegInfinite_unpackedbf :
    int -> int -> unpackedbf -> QFBV.QFBV.bexp **)

let isNegInfinite_unpackedbf mlen elen bf =
  QFBV.QFBV.Bconj ((isInfinite_unpackedbf mlen elen bf), bf.un_s)

(** val isSuborNor_unpackedbf : int -> int -> unpackedbf -> QFBV.QFBV.bexp **)

let isSuborNor_unpackedbf mlen elen bf =
  QFBV.QFBV.Bdisj ((isNormal_unpackedbf mlen elen bf),
    (isSubNormal_unpackedbf mlen elen bf))
