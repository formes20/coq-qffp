open EqVar
open WBCommon
open WBPacking
open WBRounding
open Ssrnat

val fixedpoint_Budiv :
  QFBV.QFBV.exp -> QFBV.QFBV.exp -> int -> QFBV.QFBV.exp * QFBV.QFBV.bexp

val div_unpackbf :
  int -> int -> (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list ->
  TypEnv.SSATE.env -> QFBV.QFBV.exp -> unpackedbf -> unpackedbf ->
  ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf
