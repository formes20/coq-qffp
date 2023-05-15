open EqVar
open NBitsDef
open WBCommon
open WBPacking
open WBRounding
open Seq
open Ssrnat

val full_fixedpoint_sqrt_sat :
  (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list -> TypEnv.SSATE.env ->
  QFBV.QFBV.exp -> int -> (((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp
  list) * QFBV.QFBV.exp) * QFBV.QFBV.bexp

val fixedpoint_sqrtB :
  (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list -> TypEnv.SSATE.env ->
  QFBV.QFBV.exp -> int -> (((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp
  list) * QFBV.QFBV.exp) * QFBV.QFBV.bexp

val sqrt_unpackbf :
  int -> int -> (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list ->
  TypEnv.SSATE.env -> QFBV.QFBV.exp -> unpackedbf ->
  ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf
