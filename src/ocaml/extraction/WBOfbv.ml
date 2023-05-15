open EqVar
open NBitsDef
open WBCommon
open WBOffp
open WBPacking
open Ssrnat

(** val of_ubv_unpackbf :
    (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list -> TypEnv.SSATE.env
    -> QFBV.QFBV.exp -> QFBV.QFBV.exp -> int -> int -> int ->
    ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf **)

let of_ubv_unpackbf gen_var g es te rm ubv ubv_size target_elen target_mlen =
  let returnZero = is_all_zeros ubv ubv_size in
  let target_unpack_elen = unpack_elen target_mlen target_elen in
  let e = QFBV.QFBV.Econst
    (from_nat target_unpack_elen (subn ubv_size (Pervasives.succ 0)))
  in
  let (p, normal_m) =
    normalize gen_var g es te e ubv target_unpack_elen ubv_size
  in
  let (p0, normal_e) = p in
  let (p1, es0) = p0 in
  let (te0, g0) = p1 in
  let nan_flag0 = QFBV.QFBV.Bfalse in
  let un_s0 = QFBV.QFBV.Bfalse in
  let un_e0 = QFBV.QFBV.Eite (returnZero,
    (defaultExponent_ext target_unpack_elen), normal_e)
  in
  let un_m0 = QFBV.QFBV.Eite (returnZero, (defaultSignificand_ext ubv_size),
    normal_m)
  in
  let ubf = { inf_flag = QFBV.QFBV.Bfalse; zero_flag = returnZero; nan_flag =
    nan_flag0; un_s = un_s0; un_e = un_e0; un_m = un_m0 }
  in
  of_unpackbf' gen_var g0 es0 te0 rm ubf target_unpack_elen ubv_size
    target_elen target_mlen

(** val of_sbv_unpackbf :
    (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list -> TypEnv.SSATE.env
    -> QFBV.QFBV.exp -> QFBV.QFBV.exp -> int -> int -> int ->
    ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf **)

let of_sbv_unpackbf gen_var g es te rm sbv sbv_size target_elen target_mlen =
  let s = msb_bexp sbv in
  let returnZero =
    is_all_zeros (QFBV.QFBV.Eunop ((QFBV.QFBV.Ulow
      (subn sbv_size (Pervasives.succ 0))), sbv))
      (subn sbv_size (Pervasives.succ 0))
  in
  let target_unpack_elen = unpack_elen target_mlen target_elen in
  let e = QFBV.QFBV.Econst (from_nat target_unpack_elen sbv_size) in
  let ext_sbv = QFBV.QFBV.Eunop ((QFBV.QFBV.Usext (Pervasives.succ 0)), sbv)
  in
  let m = QFBV.QFBV.Eite (s, (QFBV.QFBV.Eunop (QFBV.QFBV.Uneg, ext_sbv)),
    ext_sbv)
  in
  let m_size = addn sbv_size (Pervasives.succ 0) in
  let (p, normal_m) = normalize gen_var g es te e m target_unpack_elen m_size
  in
  let (p0, normal_e) = p in
  let (p1, es0) = p0 in
  let (te0, g0) = p1 in
  let nan_flag0 = QFBV.QFBV.Bfalse in
  let un_e0 = QFBV.QFBV.Eite (returnZero,
    (defaultExponent_ext target_unpack_elen), normal_e)
  in
  let un_m0 = QFBV.QFBV.Eite (returnZero, (defaultSignificand_ext m_size),
    normal_m)
  in
  let ubf = { inf_flag = QFBV.QFBV.Bfalse; zero_flag = returnZero; nan_flag =
    nan_flag0; un_s = s; un_e = un_e0; un_m = un_m0 }
  in
  of_unpackbf' gen_var g0 es0 te0 rm ubf target_unpack_elen m_size
    target_elen target_mlen
