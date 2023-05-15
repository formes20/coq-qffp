From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From ssrlib Require Import EqVar.
From Coq Require Import ZArith.
From nbits Require Import NBits.
From BitBlasting Require Import Typ TypEnv State.
From BitBlasting Require Import QFBV.
From WordBlasting Require Import WBCommon WBPacking WBRounding.

Import QFBV.
Import QFBVNotation.

Section Tobv.

  Variable mlen elen: nat.
  
  Notation unpack_elen := (unpack_elen mlen elen).
  Notation unpack_mlen := (unpack_mlen mlen).
  Notation defaultExponent := (defaultExponent mlen elen).
  Notation defaultSignificand := (defaultSignificand mlen).
  Notation round := (round mlen elen).
  Notation make_unpackedbf_var := ( make_unpackedbf_var mlen elen).
  
  Definition round_fixedpoint (rm : exp) (s : bexp) (m : exp) (target_len : nat) (m_size : nat): exp * bexp :=
    let guard_bit_pos := m_size - target_len - 1 in
    let guard_bit := is_Btrue (Eunop (Uextr guard_bit_pos guard_bit_pos) m) in
    let sticky_bit := ~~# (is_all_zeros (Eunop (Uextr (guard_bit_pos-1) 0) m) guard_bit_pos) in
    let unrounded_m := Eunop (Uextr (m_size - 1) (m_size - target_len)) m in
    let is_even := lsb_bexp unrounded_m in
    let up := roundUp rm s is_even guard_bit sticky_bit in
    let (succ_m, ovf) := Bsucc unrounded_m target_len in
      ((Eite up succ_m unrounded_m), (Eite_bexp up ovf Bfalse)).
      
  Definition to_bv_unpackbf (rm : exp) (is_zero s : bexp) (e m : exp) (target_len : nat) : exp * bexp :=
    let max_shift := target_len + 1 in
    let ms_size := (Nat.log2_up (max_shift)) in
    let zero_m := Ebinop Band m (Eite is_zero (zero_exp unpack_mlen) (ones_exp unpack_mlen)) in
    let ext_m := Eunop (Uzext max_shift) zero_m in
    let m_size := unpack_mlen + max_shift in
    let ext_m := if ms_size > m_size then Eunop (Uzext (ms_size - m_size)) ext_m else ext_m in
    let m_size := if ms_size > m_size then ms_size else m_size in 
    let ext_e := Eunop (Usext (m_size - unpack_elen)) e in  (* extended to m_size *)
    let shift_amount := Ebinop Badd ext_e (Econst (from_nat m_size 2)) in
    let shift_amount := Eite (shift_amount <s?# (zero_exp (m_size))) (zero_exp m_size) shift_amount in
    let ms_exp := Econst (from_nat m_size max_shift) in
    let shift_amount := Eite (shift_amount >s?# ms_exp) ms_exp shift_amount in
    let shifted_m := Ebinop Bshl ext_m shift_amount in
      round_fixedpoint rm s shifted_m target_len m_size.
  
  Definition to_ubv_unpackbf (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (rm : exp) (bf : unpackedbf) (target_len : nat) : SSATE.env * nat * seq bexp * exp :=
     let (v, g) := gen_var g in
     let te := SSATE.add v (Tuint target_len) te in
     let inval := Evar v in
     let returnInval := (nan_flag bf) \/# (inf_flag bf) in
     let s := un_s bf in
     let e := un_e bf in
     let m := un_m bf in
     let tl_size := (Nat.log2_up (target_len + 1)) + 1 in
     let tl_exp := if tl_size > unpack_elen then Econst (from_nat tl_size target_len)
                   else Econst (from_nat unpack_elen target_len) in
     let match_e := if tl_size > unpack_elen then Eunop (Usext (tl_size - unpack_elen)) e else e in
     let match_e_size := if tl_size > unpack_elen then tl_size else unpack_elen in
     let too_large := (match_e >=s?# tl_exp) in
     let too_negative := s /\# (~~# (zero_flag bf)) /\# (match_e >=s?# (zero_exp match_e_size)) in
     let returnInval := returnInval \/# too_large \/# too_negative in
     let (result, overflow) := to_bv_unpackbf rm (zero_flag bf) s e m target_len in
     let returnInval := returnInval \/# overflow in
     let '(te, g, es, result) := make_exp_var gen_var g es te (Eite returnInval inval result) target_len in 
        (te, g, es, result).
      
  Definition to_sbv_unpackbf (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (rm : exp) (bf : unpackedbf) (target_len : nat) : SSATE.env * nat * seq bexp * exp :=
   let (v, g) := gen_var g in
   let te := SSATE.add v (Tuint target_len) te in
   let inval := Evar v in
   let returnInval := (nan_flag bf) \/# (inf_flag bf) in
   let s := un_s bf in
   let e := un_e bf in
   let m := un_m bf in
   let tl_size := (Nat.log2_up (target_len + 1)) + 1 in
   let tl_exp := if tl_size > unpack_elen then Econst (from_nat tl_size target_len)
                 else Econst (from_nat unpack_elen target_len) in
   let match_e := if tl_size > unpack_elen then Eunop (Usext (tl_size - unpack_elen)) e else e in
   let match_e_size := if tl_size > unpack_elen then tl_size else unpack_elen in
   let too_large := (match_e >=s?# tl_exp) in
   let returnInval := returnInval \/# too_large in
   let (result, overflow) := to_bv_unpackbf rm (zero_flag bf) s e m target_len in
   let overflow := overflow \/# 
                   ((msb_bexp result) /\# 
                    (~~# (s /\# (is_all_zeros (Eunop (Uextr (target_len-2) 0) result) (target_len-1))))) in
   let returnInval := returnInval \/# overflow in
   let correct_result := Eite s (Eunop Uneg result) result in
   let '(te, g, es, result) := make_exp_var gen_var g es te (Eite returnInval inval correct_result) target_len in 
    (te, g, es, result).
      
  Notation unpack := (unpack mlen elen).
  Notation pack := (pack mlen elen).
  
  Definition to_ubv (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (rm : exp) (s e m : exp) (target_len : nat) : SSATE.env * nat * seq bexp * exp :=
  let '(te, g, es, ubf) := unpack gen_var g es te s e m in
  let '(te, g, es, result) := to_ubv_unpackbf gen_var g es te rm ubf target_len in
    (te, g, es, result).
    
  Definition to_sbv  (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (rm : exp) (s e m : exp) (target_len : nat) : SSATE.env * nat * seq bexp * exp :=
  let '(te, g, es, ubf) := unpack gen_var g es te s e m in
  let '(te, g, es, result) := to_sbv_unpackbf gen_var g es te rm ubf target_len in
    (te, g, es, result).

End Tobv.
