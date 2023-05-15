From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From ssrlib Require Import EqVar.
From Coq Require Import ZArith.
From nbits Require Import NBits.
From BitBlasting Require Import Typ TypEnv State.
From BitBlasting Require Import QFBV.
From WordBlasting Require Import WBCommon WBPacking WBOffp.

Import QFBV.
Import QFBVNotation.

Section Ofbv.

  Variable mlen elen: nat.
  
   (* If the unpackbf in the target format cannot be stored, positive infinity is returned *)
   Definition of_ubv_unpackbf (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (rm : exp) (ubv : exp) (ubv_size: nat) (target_elen target_mlen : nat) : SSATE.env * nat * seq bexp * unpackedbf :=
      let returnZero := is_all_zeros ubv ubv_size in
      let target_unpack_elen := unpack_elen target_mlen target_elen in
      let target_unpack_mlen := unpack_mlen target_mlen in
      let e := Econst (from_nat target_unpack_elen (ubv_size-1)) in
      let e_size := target_unpack_elen in
      let m_size := ubv_size in
      let '(te, g, es, normal_e, normal_m) := normalize gen_var g es te e ubv e_size m_size in
      let inf_flag := Bfalse in
      let zero_flag := returnZero in
      let nan_flag := Bfalse in
      let un_s := Bfalse in
      let un_e := Eite returnZero (defaultExponent_ext e_size) normal_e in
      let un_m := Eite returnZero (defaultSignificand_ext m_size) normal_m in
      let ubf := Build_unpackedbf Bfalse zero_flag nan_flag un_s un_e un_m in
        of_unpackbf' gen_var g es te rm ubf e_size m_size target_elen target_mlen.
        
   Definition of_sbv_unpackbf (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (rm : exp) (sbv : exp) (sbv_size: nat) (target_elen target_mlen : nat) : SSATE.env * nat * seq bexp * unpackedbf :=
      let s := msb_bexp sbv in
      let returnZero := is_all_zeros (Eunop (Ulow (sbv_size-1)) sbv) (sbv_size-1) in
      let target_unpack_elen := unpack_elen target_mlen target_elen in
      let target_unpack_mlen := unpack_mlen target_mlen in
      let e := Econst (from_nat target_unpack_elen sbv_size) in
      let e_size := target_unpack_elen in
      let ext_sbv := Eunop (Usext 1) sbv in    (* The original sign bit is treated as a numerir bit *)
      let m := Eite s (Eunop Uneg ext_sbv) ext_sbv in
      let m_size := sbv_size + 1 in
      let '(te, g, es, normal_e, normal_m) := normalize gen_var g es te e m e_size m_size in
      let inf_flag := Bfalse in
      let zero_flag := returnZero in
      let nan_flag := Bfalse in
      let un_s := s in
      let un_e := Eite returnZero (defaultExponent_ext e_size) normal_e in
      let un_m := Eite returnZero (defaultSignificand_ext m_size) normal_m in
      let ubf := Build_unpackedbf Bfalse zero_flag nan_flag un_s un_e un_m in
        of_unpackbf' gen_var g es te rm ubf e_size m_size target_elen target_mlen.

   (* fp.to_fp_unsigned (RM, BV, FP) *)
   Definition of_ubv (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (rm : exp) (ubv : exp) (ubv_size: nat) (target_elen target_mlen : nat) : SSATE.env * nat * seq bexp * (exp * exp * exp) :=
      let '(te, g, es, unpack_result) := of_ubv_unpackbf gen_var g es te rm ubv ubv_size target_elen target_mlen in
      let repack_result := pack target_mlen target_elen unpack_result in
        (te, g, es, repack_result).
        
   (* fp.to_fp (RM, BV, FP) *)
   Definition of_sbv (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (rm : exp) (sbv : exp) (sbv_size: nat) (target_elen target_mlen : nat) : SSATE.env * nat * seq bexp * (exp * exp * exp) :=
      let '(te, g, es, unpack_result) := of_sbv_unpackbf gen_var g es te rm sbv sbv_size target_elen target_mlen in
      let repack_result := pack target_mlen target_elen unpack_result in
        (te, g, es, repack_result).

End Ofbv.
