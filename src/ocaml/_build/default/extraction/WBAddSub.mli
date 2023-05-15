open EqVar
open WBCommon
open WBPacking
open WBRounding
open Ssrnat

val addSign :
  QFBV.QFBV.exp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp

val subSign :
  QFBV.QFBV.exp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp

val sticky_ashrB :
  QFBV.QFBV.exp -> QFBV.QFBV.exp -> int -> int ->
  QFBV.QFBV.exp * QFBV.QFBV.bexp

val add_unpackbf' :
  int -> int -> (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list ->
  TypEnv.SSATE.env -> QFBV.QFBV.exp -> unpackedbf -> unpackedbf ->
  QFBV.QFBV.bexp -> ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp
  list) * unpackedbf

val add_unpackbf :
  int -> int -> (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list ->
  TypEnv.SSATE.env -> QFBV.QFBV.exp -> unpackedbf -> unpackedbf ->
  ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf

val sub_unpackbf :
  int -> int -> (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list ->
  TypEnv.SSATE.env -> QFBV.QFBV.exp -> unpackedbf -> unpackedbf ->
  ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf
