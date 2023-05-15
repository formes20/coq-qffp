From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From ssrlib Require Import EqVar.
From Coq Require Import ZArith.
From nbits Require Import NBits.
From BitBlasting Require Import Typ TypEnv State.
From BitBlasting Require Import QFBV.
From WordBlasting Require Import WBCommon WBPacking.

Import QFBV.
Import QFBVNotation.

Section Rounding.

  Variable mlen elen: nat.
  
  Notation unpack_elen := (unpack_elen mlen elen).
  Notation unpack_mlen := (unpack_mlen mlen).
  Notation unpack_mlen_Z := (unpack_mlen_Z mlen).
  Notation defaultExponent := (defaultExponent mlen elen).
  Notation defaultSignificand := (defaultSignificand mlen).
  Notation is_overflow_bexp := (is_overflow_bexp mlen elen).
  Notation is_underflow_bexp := (is_underflow_bexp mlen elen).
  Notation min_subnormal_e_exp := (min_subnormal_e_exp mlen elen).
  Notation min_normal_e_exp := (min_normal_e_exp mlen elen).
  Notation max_subnormal_e := (max_subnormal_e elen).
  Notation max_normal_e_exp := (max_normal_e_exp mlen elen).
  Notation min_signficand_exp := (min_signficand_exp mlen).
  Notation max_signficand_exp := (max_signficand_exp mlen).
  
  Definition rne_exp : exp := Econst [::false;false;false].
  Definition rna_exp : exp := Econst [::true;false;false].
  Definition rtp_exp : exp := Econst [::false;true;false].
  Definition rtn_exp : exp := Econst [::true;true;false].
  Definition rtz_exp : exp := Econst [::false;false;true].
  
  Definition roundUp (rm : exp) (s is_even guard_bit sticky_bit : bexp) : bexp :=
    ((rm =?# rne_exp) /\# guard_bit /\# (sticky_bit \/# (~~# is_even))) \/#
    ((rm =?# rna_exp) /\# guard_bit) \/#
    ((rm =?# rtp_exp) /\# (~~# s) /\# (guard_bit \/# sticky_bit)) \/#
    ((rm =?# rtn_exp) /\# s /\# (guard_bit \/# sticky_bit)) \/#
    ((rm =?# rtz_exp) /\# Bfalse).
      
  Definition round (rm : exp) (zs : bexp) (isZero s : bexp) (e m : exp) (e_size m_size : nat) :  unpackedbf :=
    let pre_overflow := is_overflow_bexp e e_size in
    (* e maybe round up *)
    let pre_underflow := e <s?# (Ebinop Bsub (Eunop (Usext (e_size - unpack_elen)) min_subnormal_e_exp) (one_exp e_size)) in
    let min_normal_e_exp_ext := Eunop (Usext (e_size - unpack_elen)) min_normal_e_exp in
    let isNormal := (min_normal_e_exp_ext <=s?# e) in
    (* Normal rounding *)
    let unrounded_m := Eunop (Uhigh unpack_mlen) m in
    let nor_guard_bit_pos := m_size - unpack_mlen - 1 in
    let nor_guard_bit := is_Btrue (Eunop (Uextr nor_guard_bit_pos nor_guard_bit_pos) m) in
    let nor_sticky_bit := ~~# (is_all_zeros (Eunop (Uextr (nor_guard_bit_pos-1) 0) m) nor_guard_bit_pos) in
    let (nor_succ_m, nor_m_ovf) := Bsucc unrounded_m unpack_mlen in
    let nor_succ_m := Eite nor_m_ovf (Econst ((zeros (unpack_mlen-1)) ++ [::true])) nor_succ_m in
    (* Subnormal rounding *)
    let shift_amount := Ebinop Bsub (Econst (from_Z e_size max_subnormal_e)) e in
    let not_subnor := shift_amount <=s?# (zero_exp e_size) in
    let subnor_underflow := shift_amount >=s?# Econst (from_Z e_size unpack_mlen_Z) in
    let shift_amount := Eite (not_subnor \/# subnor_underflow) (zero_exp e_size) shift_amount in
    (* suppose that unpack_mlen > e_size *)
    let shift_amount := Eunop (Uzext (unpack_mlen - e_size)) shift_amount in
    let subnor_guard_pos := Ebinop Bshl (one_exp unpack_mlen) shift_amount in
    let subnor_guard_bit := ~~# (is_all_zeros (Ebinop Band unrounded_m subnor_guard_pos) unpack_mlen) in
    let sticky_mask := Ebinop Bsub subnor_guard_pos (one_exp unpack_mlen) in
    let subnor_sticky_bit := nor_guard_bit \/# nor_sticky_bit \/#
                             (~~# (is_all_zeros (Ebinop Band unrounded_m sticky_mask) unpack_mlen)) in
    (* unsafe cases are catch by subnor_underflow *)
    let subnor_lsb_pos := Ebinop Bshl subnor_guard_pos (one_exp unpack_mlen) in
    let mask := Ebinop Bor subnor_guard_pos sticky_mask in
    let inv_mask := Eunop Unot mask in
    let subnor_significand := Ebinop Band unrounded_m inv_mask in
    let subnor_succ_m := Ebinop Badd subnor_significand subnor_lsb_pos in
    let subnor_m_ovf := is_all_zeros subnor_succ_m unpack_mlen in
    let subnor_succ_m := Eite subnor_m_ovf
                           (Econst ((zeros (unpack_mlen-1)) ++ [::true])) subnor_succ_m in
    (* total *)
    let guard_bit := Eite_bexp isNormal nor_guard_bit subnor_guard_bit in
    let sticky_bit := Eite_bexp isNormal nor_sticky_bit subnor_sticky_bit in
    let is_even := Eite_bexp isNormal (~~# (lsb_bexp unrounded_m)) (is_all_zeros (Ebinop Band unrounded_m subnor_lsb_pos) unpack_mlen) in
    let m_up := roundUp rm s is_even guard_bit sticky_bit in
    let rounded_m := Eite isNormal 
                       (Eite m_up nor_succ_m unrounded_m)
                       (Eite m_up subnor_succ_m subnor_significand) in
    (* deal with exp *)
    let ext_e := Eunop (Usext 1) e in
    let e_up := m_up /\# (Eite_bexp isNormal nor_m_ovf subnor_m_ovf) in
    let correct_e := Eite e_up (Ebinop Badd ext_e (one_exp (e_size + 1))) ext_e in
    let post_overflow := is_overflow_bexp correct_e (e_size + 1) in
    let post_underflow := is_underflow_bexp correct_e (e_size + 1) in
    let overflow := Eite_bexp pre_overflow Btrue post_overflow in
    let underflow := Eite_bexp pre_underflow Btrue post_underflow in
    let rounded_e := Eunop (Ulow unpack_elen) correct_e in
    (* construct result *)
    let returnZero := (rm =?# rne_exp) \/# (rm =?# rna_exp) \/# (rm =?# rtz_exp) \/#
                      ((rm =?# rtp_exp) /\# s) \/#
                      ((rm =?# rtn_exp) /\# (~~# s)) in
    let returnInf := (rm =?# rne_exp) \/# (rm =?# rna_exp) \/# 
                     ((rm =?# rtp_exp) /\# (~~# s)) \/#
                     ((rm =?# rtn_exp) /\# s) in
    let inf_flag := Eite_bexp overflow returnInf Bfalse in
    let zero_flag := Eite_bexp isZero Btrue (Eite_bexp underflow returnZero Bfalse) in
    let nan_flag := Bfalse in
    let un_s := Eite_bexp isZero s (Eite_bexp zero_flag zs s) in
    let un_e := Eite isZero defaultExponent
                  (Eite underflow
                   (Eite returnZero defaultExponent min_subnormal_e_exp)
                   (Eite overflow 
                     (Eite returnInf defaultExponent max_normal_e_exp) 
                       rounded_e)) in
    let un_m := Eite isZero defaultSignificand
                  (Eite underflow 
                   (Eite returnZero defaultSignificand min_signficand_exp)
                   (Eite overflow 
                     (Eite returnInf defaultSignificand max_signficand_exp)
                        rounded_m)) in
      Build_unpackedbf inf_flag zero_flag nan_flag un_s un_e un_m.
        
End Rounding.
