open BinInt
open BinNums
open Datatypes
open EqVar
open NBitsDef
open WBAddSub
open WBCommon
open WBPacking
open WBRounding
open Ssrnat

val divide_step :
  QFBV.QFBV.exp -> QFBV.QFBV.exp -> int -> QFBV.QFBV.exp * QFBV.QFBV.bexp

val divide_loop :
  (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list -> TypEnv.SSATE.env ->
  QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.exp -> int -> int -> int ->
  ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * QFBV.QFBV.exp

val remrne_unpackbf :
  int -> int -> (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list ->
  TypEnv.SSATE.env -> unpackedbf -> unpackedbf ->
  ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf
