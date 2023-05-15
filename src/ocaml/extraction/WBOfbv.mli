open EqVar
open NBitsDef
open WBCommon
open WBOffp
open WBPacking
open Ssrnat

val of_ubv_unpackbf :
  (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list -> TypEnv.SSATE.env ->
  QFBV.QFBV.exp -> QFBV.QFBV.exp -> int -> int -> int ->
  ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf

val of_sbv_unpackbf :
  (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list -> TypEnv.SSATE.env ->
  QFBV.QFBV.exp -> QFBV.QFBV.exp -> int -> int -> int ->
  ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf
