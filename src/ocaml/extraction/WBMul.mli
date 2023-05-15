open EqVar
open WBCommon
open WBPacking
open WBRounding
open Ssrnat

val xorSign : QFBV.QFBV.bexp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp

val mul_unpackbf :
  int -> int -> (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list ->
  TypEnv.SSATE.env -> QFBV.QFBV.exp -> unpackedbf -> unpackedbf ->
  ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf
