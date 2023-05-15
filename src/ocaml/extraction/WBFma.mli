open EqVar
open WBAddSub
open WBCommon
open WBMul
open WBPacking
open WBRounding
open Ssrnat

val mul_unpackbf_noround :
  int -> int -> (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list ->
  TypEnv.SSATE.env -> unpackedbf -> unpackedbf ->
  ((((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp
  list) * unpackedbf) * int) * int

val add_ext_unpackbf :
  int -> int -> (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list ->
  TypEnv.SSATE.env -> QFBV.QFBV.exp -> unpackedbf -> unpackedbf ->
  QFBV.QFBV.bexp -> int -> int -> ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp
  list) * unpackedbf

val fma_unpackbf :
  int -> int -> (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list ->
  TypEnv.SSATE.env -> QFBV.QFBV.exp -> unpackedbf -> unpackedbf -> unpackedbf
  -> ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf
