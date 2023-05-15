From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From ssrlib Require Import EqVar.
From Coq Require Import ZArith.
From nbits Require Import NBits.
From BitBlasting Require Import Typ TypEnv State.
From BitBlasting Require Import QFBV.
From WordBlasting Require Import WBCommon WBPacking WBRounding.

Import QFBV.
Import QFBVNotation.

Section Sqrt.

  Variable mlen elen: nat.
  
  Notation unpack_elen := (unpack_elen mlen elen).
  Notation unpack_mlen := (unpack_mlen mlen).
  Notation defaultExponent := (defaultExponent mlen elen).
  Notation defaultSignificand := (defaultSignificand mlen).
  Notation round := (round mlen elen).
  Notation make_unpackedbf_var := ( make_unpackedbf_var mlen elen).
  
  Fixpoint full_fixedpoint_sqrt (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (comp result : exp) (result_size : nat) (loc : nat) : SSATE.env * nat * seq bexp * exp * bexp :=
    match loc with
    | 0 => let ext_result := Eunop (Uzext result_size) result in
           let product := Ebinop Bmul ext_result ext_result in
           let remainder_bit := ~~# (product =?# comp) in
            (te, g, es, result, remainder_bit)
    | S loc' => let shift := Econst (shlB (loc'-1) ([::true] ++ (zeros (result_size-1)))) in
                let candidate_result := Ebinop Bor result shift in
                let ext_candidate_result := Eunop (Uzext result_size) candidate_result in
                let product := Ebinop Bmul ext_candidate_result ext_candidate_result in
                let next_result := Eite (product <=u?# comp) candidate_result result in
                let '(te, g, es, next_result) := make_exp_var gen_var g es te next_result result_size in
                  full_fixedpoint_sqrt gen_var g es te comp next_result result_size loc'
    end.
    
  Definition full_fixedpoint_sqrt_sat (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (comp : exp) (result_size : nat) : SSATE.env * nat * seq bexp * exp * bexp :=
    let '(te, g, es, sqrt_m) := make_Evar gen_var g es te result_size in
    let range_limit := (sqrt_m >=u?# Econst ((zeros (result_size-1) ++ [::true]))) in
    let ext_sqrt_m := Eunop (Uzext result_size) sqrt_m in
    let lower_product := Ebinop Bmul ext_sqrt_m ext_sqrt_m in
    let succ_sqrt_m := Ebinop Badd sqrt_m (one_exp result_size) in
    let ext_succ_sqrt_m := Eunop (Uzext result_size) succ_sqrt_m in
    let higher_product := Ebinop Bmul ext_succ_sqrt_m ext_succ_sqrt_m in
    let sqrt_limit := Eite_bexp (is_all_ones sqrt_m result_size)
                        (lower_product <=u?# comp)
                        ( (lower_product <=u?# comp) /\# (higher_product >u?# comp) ) in
    let remainder_bit := ~~# (lower_product =?# comp) in
    let es := range_limit :: sqrt_limit :: es in
      (te, g, es, sqrt_m, remainder_bit).
  
  (* argument - bs : [1,4), 
     return - result : [1,2) with length of (bs_size-1) 
              remainder_bit : bool *)
  Definition fixedpoint_sqrtB (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (bs : exp) (bs_size : nat) : SSATE.env * nat * seq bexp * exp * bexp :=
    let ext_bs := (zero_exp (bs_size-2)) ++# bs in
(*     let candidate_result := Econst (zeros (bs_size-2) ++ [::true]) in
      full_fixedpoint_sqrt gen_var g es te ext_bs candidate_result (bs_size-1) (bs_size-1). *)
      full_fixedpoint_sqrt_sat gen_var g es te ext_bs (bs_size-1).
      
  Definition sqrt_unpackbf (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (rm : exp) (bf : unpackedbf) : SSATE.env * nat * seq bexp * unpackedbf :=
    let returnNaN := ((nan_flag bf) \/# (un_s bf)) /\# (~~#(zero_flag bf)) in
    let returnInf := inf_flag bf /\# (~~# (un_s bf)) in
    let returnZero := zero_flag bf in
    let s := un_s bf in
    let e := un_e bf in
    let m := un_m bf in 
    let is_e_odd := lsb_bexp e in
    let e_size := unpack_elen in
    let halved_e := Ebinop Bashr e (one_exp e_size) in
    let ext_m := (zero_exp 1) ++# (Eunop (Uzext 1) m) in
    let m_size := unpack_mlen + 2 in
    let aligned_m := Eite is_e_odd (Ebinop Bshl ext_m (one_exp m_size)) ext_m in
    let '(te, g, es, sqrt_m, remainder_bit) := fixedpoint_sqrtB gen_var g es te aligned_m m_size in
    let sticky_bit := Eite remainder_bit (one_exp 1) (zero_exp 1) in
    let sticky_m := sticky_bit ++# sqrt_m in
    let rounded_result := round rm Bfalse returnZero Bfalse halved_e sticky_m e_size m_size in
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
                  (Eite_bexp returnZero s (un_s rounded_result)) in
    let un_e := Eite (returnNaN \/# returnInf \/# returnZero) defaultExponent
                  (un_e rounded_result) in
    let un_m := Eite (returnNaN \/# returnInf \/# returnZero) defaultSignificand
                  (un_m rounded_result) in
      make_unpackedbf_var gen_var g es te inf_flag zero_flag nan_flag un_s un_e un_m.

  Notation unpack := (unpack mlen elen).
  Notation pack := (pack mlen elen).
  
  Definition sqrt (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (rm : exp) (s e m : exp) : SSATE.env * nat * seq bexp * (exp * exp * exp) :=
    let '(te, g, es, ubf) := unpack gen_var g es te s e m in
    let '(te, g, es, unpack_result) := sqrt_unpackbf gen_var g es te rm ubf in
    let repack_result := pack unpack_result in
      (te, g, es, repack_result).
      
End Sqrt.
