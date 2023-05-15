From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From ssrlib Require Import EqVar.
From Coq Require Import ZArith.
From nbits Require Import NBits.
From BitBlasting Require Import Typ TypEnv State.
From BitBlasting Require Import QFBV.
From WordBlasting Require Import WBCommon WBPacking WBRounding WBMul WBAddSub.

Import QFBV.
Import QFBVNotation.

Section Fma.

  Variable mlen elen: nat.
  
  Notation unpack_elen := (unpack_elen mlen elen).
  Notation unpack_mlen := (unpack_mlen mlen).
  Notation defaultExponent := (defaultExponent mlen elen).
  Notation defaultSignificand := (defaultSignificand mlen).
  Notation max_normal_e := (max_normal_e elen).
  Notation min_subnormal_e := (min_subnormal_e mlen elen).
  Notation round := (round mlen elen).
  Notation make_unpackedbf_var := ( make_unpackedbf_var mlen elen).
  
  Definition mul_unpackbf_noround (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (bf1 bf2 : unpackedbf) : SSATE.env * nat * seq bexp * unpackedbf * nat * nat :=
   (* special case *)
    let eitherNaN := (nan_flag bf1) \/# (nan_flag bf2) in
    let inf_zero := ((inf_flag bf1) /\# (zero_flag bf2)) \/#
                    ((zero_flag bf1) /\# (inf_flag bf2)) in
    let returnNaN := eitherNaN \/# inf_zero in
    let returnInf := (inf_flag bf1) \/# (inf_flag bf2) in
    let returnZero := (zero_flag bf1) \/# (zero_flag bf2) in
    (* normal and subnormal case *)
    let s1 := un_s bf1 in
    let e1 := un_e bf1 in
    let m1 := un_m bf1 in 
    let s2 := un_s bf2 in
    let e2 := un_e bf2 in
    let m2 := un_m bf2 in 
    let s := xorSign s1 s2 in
    let ext_m1 := Eunop (Uzext unpack_mlen) m1 in
    let ext_m2 := Eunop (Uzext unpack_mlen) m2 in
    let m_size := unpack_mlen + unpack_mlen in
    let product_m := Ebinop Bmul ext_m1 ext_m2 in
    let has_leading_one := msb_bexp product_m in
    let normal_product_m := Eite has_leading_one product_m (Ebinop Bshl product_m (one_exp m_size)) in
    let ext_e1 := Eunop (Usext 1) e1 in
    let ext_e2 := Eunop (Usext 1) e2 in
    let e_size := unpack_elen + 1 in
    let sum_e := Badc has_leading_one ext_e1 ext_e2 e_size in
    let inf_flag := returnInf in
    let zero_flag := returnZero in
    let nan_flag := returnNaN in
    let un_s := Eite_bexp returnNaN Btrue s in
    let un_e := Eite (returnNaN \/# returnInf \/# returnZero) (defaultExponent_ext e_size) sum_e in
    let un_m := Eite (returnNaN \/# returnInf \/# returnZero) (defaultSignificand_ext m_size) normal_product_m in 
    let '(te, g, es, result) := make_ext_unpackedbf_var gen_var g es te inf_flag zero_flag nan_flag un_s un_e un_m e_size m_size in
      (te, g, es, result, e_size, m_size).

  Definition add_ext_unpackbf (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (rm : exp) (bf1 bf2 : unpackedbf) (is_add : bexp) (ext_e_size ext_m_size : nat) : SSATE.env * nat * seq bexp * unpackedbf :=
    (* special case *)
    let eitherNaN := (nan_flag bf1) \/# (nan_flag bf2) in
    let bothInf := (inf_flag bf1) /\# (inf_flag bf2) in
    let diffSign := xorSign (un_s bf1) (un_s bf2) in
    let returnNaN := eitherNaN \/# (bothInf /\# diffSign) in
    let returnInf := (bothInf /\# (~~# diffSign)) \/# 
                      (xorSign (inf_flag bf1) (inf_flag bf2)) in
    let inf_sign := Eite_bexp (inf_flag bf1) (un_s bf1) (xorSign is_add (~~# (un_s bf2))) in
    let returnZero := (zero_flag bf1) /\# (zero_flag bf2) in
    let zero_sign := Eite_bexp is_add (addSign rm (un_s bf1) (un_s bf2)) (subSign rm (un_s bf1) (un_s bf2)) in
    let returnLeft := (~~#(zero_flag bf1)) /\# (zero_flag bf2) in
    let returnRight := (zero_flag bf1) /\# (~~# (zero_flag bf2)) in
    (* normal and subnormal case *)
    let s1 := un_s bf1 in
    let e1 := un_e bf1 in
    let m1 := un_m bf1 in 
    let s2 := un_s bf2 in
    let e2 := un_e bf2 in
    let m2 := un_m bf2 in 
    (* Whether the significand perform addition or subtraction *)
    let is_sign_add := xorSign (xorSign s1 s2) is_add in
    (* Compute exponent difference *)
    let ext_e1 := Eunop (Usext 1) e1 in
    let ext_e2 := Eunop (Usext 1) e2 in
    let e_size := ext_e_size + 1 in
    let e_diff := Ebinop Bsub ext_e1 ext_e2 in
    let left_e_larger := ~~# (msb_bexp e_diff) in
    let abs_e_diff := Eite left_e_larger e_diff (Eunop Uneg e_diff) in
    let larger_e := Eite left_e_larger ext_e1 ext_e2 in
    let e_diff_is_zero := e_diff =?# (zero_exp e_size) in
    let e_diff_is_one := e_diff =?# (one_exp e_size) in
    (* Swapping *)
    let left_larger := left_e_larger /\# (Eite_bexp e_diff_is_zero (m1 >=u?# m2) Btrue) in
    let larger_m := Eite left_larger m1 m2 in
    let smaller_m := Eite left_larger m2 m1 in
    (* Two extra significand bits for the guard and sticky bits and one extra bit for avoiding overflow *)
    let ext_m1 := (zero_exp 2) ++# (Eunop (Uzext 1) larger_m) in
    let ext_m2 := (zero_exp 2) ++# (Eunop (Uzext 1) smaller_m) in
    let m_size := ext_m_size + 3 in
    let result_sign := Eite_bexp left_larger s1 (xorSign (~~# is_add) s2) in
    let negated_m2 := Eite is_sign_add ext_m2 (Eunop Uneg ext_m2) in
    let (aligned_m2, shifted_stickyBit) := sticky_ashrB negated_m2 abs_e_diff m_size e_size in
    let sum := Ebinop Badd ext_m1 aligned_m2 in
    let top_bit := msb_bexp sum in
    let aligned_bit := is_Btrue (Eunop (Uextr (m_size-2) (m_size-2)) sum) in
    let lower_bit := is_Btrue (Eunop (Uextr (m_size-3) (m_size-3)) sum) in
    (* The situations of overflow or cancel *)
    let overflow := top_bit in
    let cancel := (~~# overflow) /\# (~~# aligned_bit) in
    let minor_cancel := cancel /\# lower_bit in
    let major_cancel := cancel /\# (~~# lower_bit) in
    let full_cancel := major_cancel /\# (is_all_zeros sum m_size) in
    let returnZero := returnZero \/# full_cancel in
    (* Adjust sum and exponent *)
    (* FIXME : opti *)
    let aligned_sum := Eite minor_cancel (Ebinop Bshl sum (one_exp m_size))
                       (Eite overflow (Ebinop Blshr sum (one_exp m_size)) sum) in
    let correct_e := Eite minor_cancel (Ebinop Bsub larger_e (one_exp e_size))
                       (Eite overflow (Ebinop Badd larger_e (one_exp e_size)) larger_e) in
    (* Set the sticky_bit *) 
    let aligned_stickyBit := Eite_bexp overflow (lsb_bexp sum) Bfalse in (* If sum is right shifted *)
    let sticky_bit_is_zero := e_diff_is_zero \/# e_diff_is_one in
    let sticky_bit_mask := Eite (sticky_bit_is_zero \/# major_cancel) (zero_exp m_size)
                            (Eite (shifted_stickyBit \/# aligned_stickyBit) (one_exp m_size) (zero_exp m_size)) in 
    let sticky_sum := Ebinop Bor aligned_sum sticky_bit_mask in
    let contract_sum := Eunop (Ulow (m_size-1)) sticky_sum in
    let m_size := m_size - 1 in
    let '(te, g, es, correct_e) := make_exp_var gen_var g es te correct_e e_size in
    let '(te, g, es, contract_sum) := make_exp_var gen_var g es te contract_sum m_size in 
    let '(te, g, es, normal_e, normal_m) := normalize gen_var g es te correct_e contract_sum e_size m_size in
    let rounded_result := round rm zero_sign returnZero result_sign normal_e normal_m e_size m_size in
    let left_rounded_result := round rm s1 (zero_flag bf1) s1 e1 m1 ext_e_size ext_m_size in
    let right_rounded_result := round rm s2 (zero_flag bf2) s2 e2 m2 ext_e_size ext_m_size in
    let inf_flag := Eite_bexp returnLeft (inf_flag left_rounded_result)
                    (Eite_bexp returnRight (inf_flag right_rounded_result)
                    (Eite_bexp returnNaN Bfalse
                    (Eite_bexp returnInf Btrue
                    (Eite_bexp returnZero Bfalse
                      (inf_flag rounded_result))))) in 
    let zero_flag := Eite_bexp returnLeft (zero_flag left_rounded_result)
                     (Eite_bexp returnRight (zero_flag right_rounded_result)
                     (Eite_bexp returnNaN Bfalse
                     (Eite_bexp returnInf Bfalse
                     (Eite_bexp returnZero Btrue
                      (zero_flag rounded_result))))) in
    let nan_flag := Eite_bexp returnNaN Btrue Bfalse in
    let un_s := Eite_bexp returnNaN Btrue
                (Eite_bexp returnLeft (un_s left_rounded_result)
                (Eite_bexp returnRight (Eite_bexp is_add (un_s right_rounded_result) (~~# (un_s right_rounded_result)))
                (Eite_bexp returnInf inf_sign
                (Eite_bexp returnZero zero_sign (un_s rounded_result))))) in
    let un_e := Eite returnLeft (un_e left_rounded_result)
                (Eite returnRight (un_e right_rounded_result)
                (Eite (returnNaN \/# returnInf \/# returnZero) defaultExponent
                  (un_e rounded_result))) in
    let un_m := Eite returnLeft (un_m left_rounded_result)
                (Eite returnRight (un_m right_rounded_result)
                (Eite (returnNaN \/# returnInf \/# returnZero) defaultSignificand
                  (un_m rounded_result))) in
      make_unpackedbf_var gen_var g es te inf_flag zero_flag nan_flag un_s un_e un_m.

  Definition fma_unpackbf (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (rm : exp) (mulbf1 mulbf2 addbf : unpackedbf) : SSATE.env * nat * seq bexp * unpackedbf :=
    let '(te, g, es, mul_noround_result, e_size, m_size) := mul_unpackbf_noround gen_var g es te mulbf1 mulbf2 in
    let e := un_e addbf in
    let m := un_m addbf in
    let ext_e := Eunop (Usext (e_size - unpack_elen)) e in
    let ext_m := (zero_exp (m_size - unpack_mlen)) ++# m in
    let ext_addbf := Build_unpackedbf (inf_flag addbf) (zero_flag addbf) (nan_flag addbf) 
                      (un_s addbf) ext_e ext_m in
      add_ext_unpackbf gen_var g es te rm mul_noround_result ext_addbf Btrue e_size m_size.

  Notation unpack := (unpack mlen elen).
  Notation pack := (pack mlen elen).
  
  Definition fma (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (rm : exp) (s1 e1 m1 s2 e2 m2 s3 e3 m3 : exp) : SSATE.env * nat * seq bexp * (exp * exp * exp) :=
    let '(te, g, es, umulbf1) := unpack gen_var g es te s1 e1 m1 in
    let '(te, g, es, umulbf2) := unpack gen_var g es te s2 e2 m2 in
    let '(te, g, es, uaddbf) := unpack gen_var g es te s3 e3 m3 in
    let '(te, g, es, unpack_result) := fma_unpackbf gen_var g es te rm umulbf1 umulbf2 uaddbf in
    let repack_result := pack unpack_result in
      (te, g, es, repack_result).
      
End Fma.
