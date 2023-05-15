open NBitsDef
open WBCommon
open WBPacking
open Seq
open Ssrnat

val rne_exp : QFBV.QFBV.exp

val rna_exp : QFBV.QFBV.exp

val rtp_exp : QFBV.QFBV.exp

val rtn_exp : QFBV.QFBV.exp

val rtz_exp : QFBV.QFBV.exp

val roundUp :
  QFBV.QFBV.exp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp ->
  QFBV.QFBV.bexp -> QFBV.QFBV.bexp

val round :
  int -> int -> QFBV.QFBV.exp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp ->
  QFBV.QFBV.bexp -> QFBV.QFBV.exp -> QFBV.QFBV.exp -> int -> int -> unpackedbf
