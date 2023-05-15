open EqVar
open NBitsDef
open Typ
open Seq
open Ssrnat

val make_exp_var :
  (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list -> TypEnv.SSATE.env ->
  QFBV.QFBV.exp -> int -> ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp
  list) * QFBV.QFBV.exp

val make_Evar :
  (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list -> TypEnv.SSATE.env ->
  int -> ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * QFBV.QFBV.exp

val make_bexp_var :
  (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list -> TypEnv.SSATE.env ->
  QFBV.QFBV.bexp -> ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp
  list) * QFBV.QFBV.bexp

val msb_bexp : QFBV.QFBV.exp -> QFBV.QFBV.bexp

val lsb_bexp : QFBV.QFBV.exp -> QFBV.QFBV.bexp

val zero_exp : int -> QFBV.QFBV.exp

val ones_exp : int -> QFBV.QFBV.exp

val one_exp : int -> QFBV.QFBV.exp

val is_all_zeros : QFBV.QFBV.exp -> int -> QFBV.QFBV.bexp

val is_all_ones : QFBV.QFBV.exp -> int -> QFBV.QFBV.bexp

val coq_Btrue_exp : QFBV.QFBV.exp

val coq_Bfalse_exp : QFBV.QFBV.exp

val is_Btrue : QFBV.QFBV.exp -> QFBV.QFBV.bexp

val coq_Eite_bexp :
  QFBV.QFBV.bexp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp

val coq_Bimp : QFBV.QFBV.bexp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp

val coq_Biff : QFBV.QFBV.bexp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp

val coq_Bsucc : QFBV.QFBV.exp -> int -> QFBV.QFBV.exp * QFBV.QFBV.bexp

val coq_Bxor_bexp : QFBV.QFBV.bexp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp

val coq_Badc :
  QFBV.QFBV.bexp -> QFBV.QFBV.exp -> QFBV.QFBV.exp -> int -> QFBV.QFBV.exp

val s_exp : int -> int -> QFBV.QFBV.exp -> QFBV.QFBV.exp

val e_exp : int -> int -> QFBV.QFBV.exp -> QFBV.QFBV.exp

val m_exp : int -> QFBV.QFBV.exp -> QFBV.QFBV.exp
