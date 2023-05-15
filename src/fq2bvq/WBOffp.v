From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From ssrlib Require Import EqVar.
From Coq Require Import ZArith.
From nbits Require Import NBits.
From BitBlasting Require Import Typ TypEnv State.
From BitBlasting Require Import QFBV.
From WordBlasting Require Import WBCommon WBPacking WBRounding.

Import QFBV.
Import QFBVNotation.

Section Offp.

  Variable mlen elen: nat.
  
    Definition of_unpackbf_mux (returnNaN returnInf returnZero s : bexp) (rounded_bf : unpackedbf) 
                                  (e_size m_size : nat) : unpackedbf :=
      let inf_flag := Eite_bexp returnNaN Bfalse
                (Eite_bexp returnInf Btrue
                (Eite_bexp returnZero Bfalse
                  (inf_flag rounded_bf))) in
      let zero_flag := Eite_bexp returnNaN Bfalse
                      (Eite_bexp returnInf Bfalse
                      (Eite_bexp returnZero Btrue
                        (zero_flag rounded_bf))) in
      let nan_flag := Eite_bexp returnNaN Btrue
                      (Eite_bexp returnInf Bfalse
                      (Eite_bexp returnZero Bfalse
                        (nan_flag rounded_bf))) in
      let un_s := Eite_bexp returnNaN Btrue (un_s rounded_bf) in
      let un_e := Eite (returnNaN \/# returnInf \/# returnZero) 
                    (defaultExponent_ext e_size) (un_e rounded_bf) in
      let un_m := Eite (returnNaN \/# returnInf \/# returnZero) 
                    (defaultSignificand_ext m_size) (un_m rounded_bf) in
        Build_unpackedbf inf_flag zero_flag nan_flag un_s un_e un_m.

    Definition of_unpackbf' (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (rm : exp) (bf : unpackedbf) (e_size m_size target_elen target_mlen : nat) : SSATE.env * nat * seq bexp * unpackedbf :=
      let returnNaN := nan_flag bf in
      let returnInf := inf_flag bf in
      let returnZero := zero_flag bf in
      let s := un_s bf in
      let e := un_e bf in
      let m := un_m bf in 
      let target_unpack_elen := unpack_elen target_mlen target_elen in
      let target_unpack_mlen := unpack_mlen target_mlen in
      let e_up := target_unpack_elen >= e_size in
      let m_up := target_unpack_mlen >= m_size in
      if e_up && m_up then 
        let ext_e := Eunop (Usext (target_unpack_elen - e_size)) e in
        let ext_m := (Ebinop Bconcat m (zero_exp (target_unpack_mlen - m_size))) in 
           make_ext_unpackedbf_var gen_var g es te
            (inf_flag bf) (zero_flag bf) (nan_flag bf) s ext_e ext_m target_unpack_elen target_unpack_mlen
      else if ~~ e_up && m_up then
        let ext_m := (Ebinop Bconcat m (zero_exp (target_unpack_mlen - m_size))) in
        let ext_sticky_m := (Ebinop Bconcat ext_m (zero_exp 2)) in (* as guard_bit and sticky_bit *)
        let rounded_bf := round target_mlen target_elen rm Bfalse (zero_flag bf) Bfalse e ext_m e_size (target_unpack_mlen + 2) in
        let result := of_unpackbf_mux returnNaN returnInf returnZero s rounded_bf target_unpack_elen target_unpack_mlen in
          make_ext_unpackedbf_var gen_var g es te 
            (inf_flag result) (zero_flag result) (nan_flag result) (un_s result)
            (un_e result) (un_m result) target_unpack_elen target_unpack_mlen
      else if e_up && (~~ m_up) then
        let ext_e := Eunop (Usext (target_unpack_elen - e_size)) e in
        let ext_sticky_m := (Ebinop Bconcat m (zero_exp 2)) in
        let rounded_bf := round target_mlen target_elen rm Bfalse (zero_flag bf) Bfalse ext_e ext_sticky_m target_unpack_elen (m_size + 2) in
        let result := of_unpackbf_mux returnNaN returnInf returnZero s rounded_bf target_unpack_elen target_unpack_mlen in
          make_ext_unpackedbf_var gen_var g es te 
            (inf_flag result) (zero_flag result) (nan_flag result) (un_s result)
            (un_e result) (un_m result) target_unpack_elen target_unpack_mlen
      else
        let ext_sticky_m := (Ebinop Bconcat m (zero_exp 2)) in (* as sticky_bit *)
        let rounded_bf := round target_mlen target_elen rm Bfalse (zero_flag bf) Bfalse e ext_sticky_m e_size (m_size + 2) in
        let result := of_unpackbf_mux returnNaN returnInf returnZero s rounded_bf target_unpack_elen target_unpack_mlen in
          make_ext_unpackedbf_var gen_var g es te 
            (inf_flag result) (zero_flag result) (nan_flag result) (un_s result)
            (un_e result) (un_m result) target_unpack_elen target_unpack_mlen.

    Definition of_unpackbf (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (rm : exp) (bf : unpackedbf) (elen mlen target_elen target_mlen : nat) : SSATE.env * nat * seq bexp * unpackedbf :=
      let e_size := unpack_elen mlen elen in
      let m_size := unpack_mlen mlen in
        of_unpackbf' gen_var g es te rm bf e_size m_size target_elen target_mlen.
  
   (* fp.to_fp (RM, FP, FP) *)
   Definition of_bf (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (rm : exp) (s e m : exp) (elen mlen target_elen target_mlen : nat) : SSATE.env * nat * seq bexp * (exp * exp * exp) :=
      let '(te, g, es, ubf) := unpack mlen elen gen_var g es te s e m in
      let '(te, g, es, unpack_result) := of_unpackbf gen_var g es te rm ubf elen mlen target_elen target_mlen in
      let repack_result := pack target_mlen target_elen unpack_result in
        (te, g, es, repack_result).

End Offp.
