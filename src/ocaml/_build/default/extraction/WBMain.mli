open EqVar
open WBAbsNeg
open WBAddSub
open WBClassify
open WBCommon
open WBCompare
open WBDiv
open WBFma
open WBMul
open WBOfbv
open WBOffp
open WBPacking
open WBRem
open WBRti
open WBSqrt

val feunop_denote :
  Fq2bvq.Fq2bvq.feunop -> int -> int -> (int -> ssavar * int) -> int ->
  QFBV.QFBV.bexp list -> TypEnv.SSATE.env -> unpackedbf ->
  ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf

val fermunop_denote :
  Fq2bvq.Fq2bvq.fermunop -> int -> int -> (int -> ssavar * int) -> int ->
  QFBV.QFBV.bexp list -> TypEnv.SSATE.env -> QFBV.QFBV.exp -> unpackedbf ->
  ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf

val febinop_denote :
  Fq2bvq.Fq2bvq.febinop -> int -> int -> (int -> ssavar * int) -> int ->
  QFBV.QFBV.bexp list -> TypEnv.SSATE.env -> unpackedbf -> unpackedbf ->
  ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf

val fermbinop_denote :
  Fq2bvq.Fq2bvq.fermbinop -> int -> int -> (int -> ssavar * int) -> int ->
  QFBV.QFBV.bexp list -> TypEnv.SSATE.env -> QFBV.QFBV.exp -> unpackedbf ->
  unpackedbf -> ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf

val fermtriop_denote :
  Fq2bvq.Fq2bvq.fermtriop -> int -> int -> (int -> ssavar * int) -> int ->
  QFBV.QFBV.bexp list -> TypEnv.SSATE.env -> QFBV.QFBV.exp -> unpackedbf ->
  unpackedbf -> unpackedbf -> ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp
  list) * unpackedbf

val fbunop_denote :
  Fq2bvq.Fq2bvq.fbunop -> int -> int -> unpackedbf -> QFBV.QFBV.bexp

val fbbinop_denote :
  Fq2bvq.Fq2bvq.fbbinop -> int -> int -> unpackedbf -> unpackedbf ->
  QFBV.QFBV.bexp

val word_blast_exp :
  (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list -> TypEnv.SSATE.env ->
  Fq2bvq.Fq2bvq.fp_exp -> ((((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp
  list) * unpackedbf) * int) * int

val word_blast_bexp :
  (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list -> TypEnv.SSATE.env ->
  Fq2bvq.Fq2bvq.fp_bexp -> ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp
  list) * QFBV.QFBV.bexp

val word_blast_bexps :
  (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list -> TypEnv.SSATE.env ->
  Fq2bvq.Fq2bvq.fp_bexp list -> (TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list
