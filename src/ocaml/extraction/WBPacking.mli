open BinInt
open BinNums
open EqVar
open NBitsDef
open WBCommon
open Seq
open Ssrnat

val elen_Z : int -> coq_Z

val unpack_mlen : int -> int

val unpack_mlen_Z : int -> coq_Z

val bias : int -> coq_Z

val max_normal_e : int -> coq_Z

val min_normal_e : int -> coq_Z

val max_subnormal_e : int -> coq_Z

val min_subnormal_e : int -> int -> coq_Z

val unpack_elen_Z : int -> int -> coq_Z

val unpack_elen : int -> int -> int

val bias_exp : int -> int -> QFBV.QFBV.exp

val max_normal_e_exp : int -> int -> QFBV.QFBV.exp

val min_normal_e_exp : int -> int -> QFBV.QFBV.exp

val max_subnormal_e_exp : int -> int -> QFBV.QFBV.exp

val min_subnormal_e_exp : int -> int -> QFBV.QFBV.exp

val max_signficand_exp : int -> QFBV.QFBV.exp

val min_signficand_exp : int -> QFBV.QFBV.exp

val is_in_normal_range_bexp :
  int -> int -> QFBV.QFBV.exp -> int -> QFBV.QFBV.bexp

val is_in_subnormal_range_bexp :
  int -> int -> QFBV.QFBV.exp -> int -> QFBV.QFBV.bexp

val is_overflow_bexp : int -> int -> QFBV.QFBV.exp -> int -> QFBV.QFBV.bexp

val is_underflow_bexp : int -> int -> QFBV.QFBV.exp -> int -> QFBV.QFBV.bexp

type unpackedbf = { inf_flag : QFBV.QFBV.bexp; zero_flag : QFBV.QFBV.bexp;
                    nan_flag : QFBV.QFBV.bexp; un_s : QFBV.QFBV.bexp;
                    un_e : QFBV.QFBV.exp; un_m : QFBV.QFBV.exp }

val make_unpackedbf_var :
  int -> int -> (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list ->
  TypEnv.SSATE.env -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp ->
  QFBV.QFBV.bexp -> QFBV.QFBV.exp -> QFBV.QFBV.exp ->
  ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf

val make_ext_unpackedbf_var :
  (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list -> TypEnv.SSATE.env ->
  QFBV.QFBV.bexp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp ->
  QFBV.QFBV.exp -> QFBV.QFBV.exp -> int -> int ->
  ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf

val defaultExponent : int -> int -> QFBV.QFBV.exp

val defaultExponent_ext : int -> QFBV.QFBV.exp

val defaultSignificand : int -> QFBV.QFBV.exp

val defaultSignificand_ext : int -> QFBV.QFBV.exp

val normalize_shift_amount_sat :
  (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list -> TypEnv.SSATE.env ->
  QFBV.QFBV.exp -> int -> ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp
  list) * QFBV.QFBV.exp

val normalize_sat :
  (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list -> TypEnv.SSATE.env ->
  QFBV.QFBV.exp -> QFBV.QFBV.exp -> int -> int ->
  (((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp
  list) * QFBV.QFBV.exp) * QFBV.QFBV.exp

val normalize :
  (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list -> TypEnv.SSATE.env ->
  QFBV.QFBV.exp -> QFBV.QFBV.exp -> int -> int ->
  (((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp
  list) * QFBV.QFBV.exp) * QFBV.QFBV.exp

val unpack :
  int -> int -> (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list ->
  TypEnv.SSATE.env -> QFBV.QFBV.exp -> QFBV.QFBV.exp -> QFBV.QFBV.exp ->
  ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf

val pack :
  int -> int -> unpackedbf -> (QFBV.QFBV.exp * QFBV.QFBV.exp) * QFBV.QFBV.exp
