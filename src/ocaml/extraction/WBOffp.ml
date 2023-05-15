open Datatypes
open EqVar
open WBCommon
open WBPacking
open WBRounding
open Ssrnat

(** val of_unpackbf_mux :
    QFBV.QFBV.bexp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp ->
    unpackedbf -> int -> int -> unpackedbf **)

let of_unpackbf_mux returnNaN returnInf returnZero _ rounded_bf e_size m_size =
  let inf_flag0 =
    coq_Eite_bexp returnNaN QFBV.QFBV.Bfalse
      (coq_Eite_bexp returnInf QFBV.QFBV.Btrue
        (coq_Eite_bexp returnZero QFBV.QFBV.Bfalse rounded_bf.inf_flag))
  in
  let zero_flag0 =
    coq_Eite_bexp returnNaN QFBV.QFBV.Bfalse
      (coq_Eite_bexp returnInf QFBV.QFBV.Bfalse
        (coq_Eite_bexp returnZero QFBV.QFBV.Btrue rounded_bf.zero_flag))
  in
  let nan_flag0 =
    coq_Eite_bexp returnNaN QFBV.QFBV.Btrue
      (coq_Eite_bexp returnInf QFBV.QFBV.Bfalse
        (coq_Eite_bexp returnZero QFBV.QFBV.Bfalse rounded_bf.nan_flag))
  in
  let un_s0 = coq_Eite_bexp returnNaN QFBV.QFBV.Btrue rounded_bf.un_s in
  let un_e0 = QFBV.QFBV.Eite ((QFBV.QFBV.Bdisj ((QFBV.QFBV.Bdisj (returnNaN,
    returnInf)), returnZero)), (defaultExponent_ext e_size), rounded_bf.un_e)
  in
  let un_m0 = QFBV.QFBV.Eite ((QFBV.QFBV.Bdisj ((QFBV.QFBV.Bdisj (returnNaN,
    returnInf)), returnZero)), (defaultSignificand_ext m_size),
    rounded_bf.un_m)
  in
  { inf_flag = inf_flag0; zero_flag = zero_flag0; nan_flag = nan_flag0;
  un_s = un_s0; un_e = un_e0; un_m = un_m0 }

(** val of_unpackbf' :
    (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list -> TypEnv.SSATE.env
    -> QFBV.QFBV.exp -> unpackedbf -> int -> int -> int -> int ->
    ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf **)

let of_unpackbf' gen_var g es te rm bf e_size m_size target_elen target_mlen =
  let returnNaN = bf.nan_flag in
  let returnInf = bf.inf_flag in
  let returnZero = bf.zero_flag in
  let s = bf.un_s in
  let e = bf.un_e in
  let m = bf.un_m in
  let target_unpack_elen = unpack_elen target_mlen target_elen in
  let target_unpack_mlen = unpack_mlen target_mlen in
  let e_up = leq e_size target_unpack_elen in
  let m_up = leq m_size target_unpack_mlen in
  if (&&) e_up m_up
  then let ext_e = QFBV.QFBV.Eunop ((QFBV.QFBV.Usext
         (subn target_unpack_elen e_size)), e)
       in
       let ext_m = QFBV.QFBV.Ebinop (QFBV.QFBV.Bconcat, m,
         (zero_exp (subn target_unpack_mlen m_size)))
       in
       make_ext_unpackedbf_var gen_var g es te bf.inf_flag bf.zero_flag
         bf.nan_flag s ext_e ext_m target_unpack_elen target_unpack_mlen
  else if (&&) (negb e_up) m_up
       then let ext_m = QFBV.QFBV.Ebinop (QFBV.QFBV.Bconcat, m,
              (zero_exp (subn target_unpack_mlen m_size)))
            in
            let rounded_bf =
              round target_mlen target_elen rm QFBV.QFBV.Bfalse bf.zero_flag
                QFBV.QFBV.Bfalse e ext_m e_size
                (addn target_unpack_mlen (Pervasives.succ (Pervasives.succ
                  0)))
            in
            let result =
              of_unpackbf_mux returnNaN returnInf returnZero s rounded_bf
                target_unpack_elen target_unpack_mlen
            in
            make_ext_unpackedbf_var gen_var g es te result.inf_flag
              result.zero_flag result.nan_flag result.un_s result.un_e
              result.un_m target_unpack_elen target_unpack_mlen
       else if (&&) e_up (negb m_up)
            then let ext_e = QFBV.QFBV.Eunop ((QFBV.QFBV.Usext
                   (subn target_unpack_elen e_size)), e)
                 in
                 let ext_sticky_m = QFBV.QFBV.Ebinop (QFBV.QFBV.Bconcat, m,
                   (zero_exp (Pervasives.succ (Pervasives.succ 0))))
                 in
                 let rounded_bf =
                   round target_mlen target_elen rm QFBV.QFBV.Bfalse
                     bf.zero_flag QFBV.QFBV.Bfalse ext_e ext_sticky_m
                     target_unpack_elen
                     (addn m_size (Pervasives.succ (Pervasives.succ 0)))
                 in
                 let result =
                   of_unpackbf_mux returnNaN returnInf returnZero s
                     rounded_bf target_unpack_elen target_unpack_mlen
                 in
                 make_ext_unpackedbf_var gen_var g es te result.inf_flag
                   result.zero_flag result.nan_flag result.un_s result.un_e
                   result.un_m target_unpack_elen target_unpack_mlen
            else let ext_sticky_m = QFBV.QFBV.Ebinop (QFBV.QFBV.Bconcat, m,
                   (zero_exp (Pervasives.succ (Pervasives.succ 0))))
                 in
                 let rounded_bf =
                   round target_mlen target_elen rm QFBV.QFBV.Bfalse
                     bf.zero_flag QFBV.QFBV.Bfalse e ext_sticky_m e_size
                     (addn m_size (Pervasives.succ (Pervasives.succ 0)))
                 in
                 let result =
                   of_unpackbf_mux returnNaN returnInf returnZero s
                     rounded_bf target_unpack_elen target_unpack_mlen
                 in
                 make_ext_unpackedbf_var gen_var g es te result.inf_flag
                   result.zero_flag result.nan_flag result.un_s result.un_e
                   result.un_m target_unpack_elen target_unpack_mlen

(** val of_unpackbf :
    (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list -> TypEnv.SSATE.env
    -> QFBV.QFBV.exp -> unpackedbf -> int -> int -> int -> int ->
    ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * unpackedbf **)

let of_unpackbf gen_var g es te rm bf elen mlen target_elen target_mlen =
  let e_size = unpack_elen mlen elen in
  let m_size = unpack_mlen mlen in
  of_unpackbf' gen_var g es te rm bf e_size m_size target_elen target_mlen
