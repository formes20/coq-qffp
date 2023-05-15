From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From ssrlib Require Import EqVar.
From Coq Require Import ZArith.
From nbits Require Import NBits.
From BitBlasting Require Import Typ TypEnv State.
From BitBlasting Require Import QFBV.
From WordBlasting Require Import WBCommon WBPacking WBRounding.

Import QFBV.
Import QFBVNotation.

Section Div.

  Variable mlen elen: nat.
  
  Notation unpack_elen := (unpack_elen mlen elen).
  Notation unpack_mlen := (unpack_mlen mlen).
  Notation defaultExponent := (defaultExponent mlen elen).
  Notation defaultSignificand := (defaultSignificand mlen).
  Notation round := (round mlen elen).
  Notation make_unpackedbf_var := ( make_unpackedbf_var mlen elen).
  
  Definition fixedpoint_Budiv (bs1 bs2 : exp) (bs_size : nat) : exp * bexp :=
    let ext_bs1 := (zero_exp (bs_size-1)) ++# bs1 in
    let ext_bs2 := (Eunop (Uzext (bs_size-1)) bs2) in
    let quo := Ebinop Bdiv ext_bs1 ext_bs2 in
    let rem := Ebinop Bmod ext_bs1 ext_bs2 in
    let contract_quo := Eunop (Ulow bs_size) quo in
    let has_rem := ~~# (is_all_zeros rem (bs_size + bs_size - 1)) in
      (contract_quo, has_rem).
  
  Definition div_unpackbf (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (rm : exp) (bf1 bf2 : unpackedbf) : SSATE.env * nat * seq bexp * unpackedbf :=
    (* special case *)
    let eitherNaN := (nan_flag bf1) \/# (nan_flag bf2) in
    let bothInf := (inf_flag bf1) /\# (inf_flag bf2) in
    let bothZero := (zero_flag bf1) /\# (zero_flag bf2) in
    let returnNaN := eitherNaN \/# bothInf \/# bothZero in
    let leftInf := (inf_flag bf1) /\# (~~# (inf_flag bf2)) /\# (~~# (nan_flag bf2)) in
    let rightZero := (~~# (zero_flag bf1)) /\# (~~# (nan_flag bf1)) /\# (zero_flag bf2) in
    let returnInf := leftInf \/# rightZero in
    let leftZero := (zero_flag bf1) /\# (~~# (zero_flag bf2)) /\# (~~# (nan_flag bf2)) in
    let rightInf := (~~# (inf_flag bf1)) /\# (~~# (nan_flag bf1)) /\# (inf_flag bf2) in
    let returnZero := leftZero \/# rightInf in
    (* normal and subnormal case *)
    let s1 := un_s bf1 in
    let e1 := un_e bf1 in
    let m1 := un_m bf1 in 
    let s2 := un_s bf2 in
    let e2 := un_e bf2 in
    let m2 := un_m bf2 in 
    let result_sign := Bxor_bexp s1 s2 in
    let ext_e1 := Eunop (Usext 2) e1 in
    let ext_e2 := Eunop (Usext 2) e2 in
    let e_size := unpack_elen + 2 in
    let sub_e := (Ebinop Bsub ext_e1 ext_e2) in
    (* for guard_bit and sticky bit *)
    let ext_m1 := (zero_exp 2) ++# m1 in 
    let ext_m2 := (zero_exp 2) ++# m2 in
    let m_size := unpack_mlen + 2 in
    let (div_m, rem_sticky_bit) := fixedpoint_Budiv ext_m1 ext_m2 m_size in
    let cancel := ~~# (msb_bexp div_m) in
    let aligned_m := Eite cancel (Ebinop Bshl div_m (one_exp m_size)) div_m in
    let aligned_e := Eite cancel (Ebinop Bsub sub_e (one_exp e_size)) sub_e in
    let mask := Eite rem_sticky_bit (one_exp m_size) (zero_exp m_size) in
    let sticky_m := Ebinop Bor aligned_m mask in
    let rounded_result := round rm result_sign returnZero result_sign aligned_e sticky_m e_size m_size in
    let inf_flag := Eite_bexp returnNaN Bfalse
                    (Eite_bexp returnInf Btrue
                    (Eite_bexp returnZero Bfalse
                      (inf_flag rounded_result))) in
    let zero_flag := Eite_bexp returnNaN Bfalse
                    (Eite_bexp returnInf Bfalse
                    (Eite_bexp returnZero Btrue
                      (zero_flag rounded_result))) in
    let nan_flag := Eite_bexp returnNaN Btrue Bfalse in
    let un_s := Eite_bexp returnNaN Btrue
                  (Eite_bexp (returnInf \/# returnZero) result_sign (un_s rounded_result)) in
    let un_e := Eite (returnNaN \/# returnInf \/# returnZero) defaultExponent
                  (un_e rounded_result) in
    let un_m := Eite (returnNaN \/# returnInf \/# returnZero) defaultSignificand
                  (un_m rounded_result) in
      make_unpackedbf_var gen_var g es te inf_flag zero_flag nan_flag un_s un_e un_m.
      
  Notation unpack := (unpack mlen elen).
  Notation pack := (pack mlen elen).
  
  Definition div (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (rm : exp) (s1 e1 m1 s2 e2 m2 : exp) : SSATE.env * nat * seq bexp * (exp * exp * exp) :=
    let '(te, g, es, ubf1) := unpack gen_var g es te s1 e1 m1 in
    let '(te, g, es, ubf2) := unpack gen_var g es te s2 e2 m2 in
    let '(te, g, es, unpack_result) := div_unpackbf gen_var g es te rm ubf1 ubf2 in
    let repack_result := pack unpack_result in
      (te, g, es, repack_result).
      
End Div.
