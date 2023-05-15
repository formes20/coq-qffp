open Datatypes
open EqVar
open WBCommon
open WBPacking
open WBRounding
open Ssrnat

val of_unpackbf_mux :
  QFBV.QFBV.bexp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp ->
  unpackedbf -> int -> int -> unpackedbf

val of_unpackbf' :
  (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list -> TypEnv.SSATE.env ->
  QFBV.QFBV.exp -> unpackedbf -> int -> int -> int -> int ->
  ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf

val of_unpackbf :
  (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list -> TypEnv.SSATE.env ->
  QFBV.QFBV.exp -> unpackedbf -> int -> int -> int -> int ->
  ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf
