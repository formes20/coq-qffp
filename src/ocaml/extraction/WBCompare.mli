open EqVar
open WBClassify
open WBCommon
open WBPacking

val eq_unpackedbf : int -> int -> unpackedbf -> unpackedbf -> QFBV.QFBV.bexp

val lt_unpackedbf : int -> int -> unpackedbf -> unpackedbf -> QFBV.QFBV.bexp

val le_unpackedbf : int -> int -> unpackedbf -> unpackedbf -> QFBV.QFBV.bexp

val gt_unpackedbf : int -> int -> unpackedbf -> unpackedbf -> QFBV.QFBV.bexp

val ge_unpackedbf : int -> int -> unpackedbf -> unpackedbf -> QFBV.QFBV.bexp

val max_unpackedbf :
  int -> int -> (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list ->
  TypEnv.SSATE.env -> unpackedbf -> unpackedbf ->
  ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf

val min_unpackedbf :
  int -> int -> (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list ->
  TypEnv.SSATE.env -> unpackedbf -> unpackedbf ->
  ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf
