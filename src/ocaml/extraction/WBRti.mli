open BinInt
open EqVar
open NBitsDef
open WBCommon
open WBPacking
open WBRounding
open Ssrnat

val roundToIntegral_unpackbf :
  int -> int -> (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list ->
  TypEnv.SSATE.env -> QFBV.QFBV.exp -> unpackedbf ->
  ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf
