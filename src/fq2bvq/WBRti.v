From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From ssrlib Require Import EqVar.
From Coq Require Import ZArith.
From nbits Require Import NBits.
From BitBlasting Require Import Typ TypEnv State.
From BitBlasting Require Import QFBV.
From WordBlasting Require Import WBCommon WBPacking WBRounding.

Import QFBV.
Import QFBVNotation.

Section Rti.

  Variable mlen elen: nat.
  
  Notation unpack_elen := (unpack_elen mlen elen).
  Notation unpack_mlen := (unpack_mlen mlen).
  Notation defaultExponent := (defaultExponent mlen elen).
  Notation defaultSignificand := (defaultSignificand mlen).
  Notation round := (round mlen elen).
  Notation make_unpackedbf_var := ( make_unpackedbf_var mlen elen).
  
  Definition roundToIntegral_unpackbf (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (rm : exp) (bf : unpackedbf) : SSATE.env * nat * seq bexp * unpackedbf :=
    let s := un_s bf in
    let e := un_e bf in
    let m := un_m bf in
    let mlen_exp := Econst(from_Z unpack_elen (Z.of_nat mlen)) in
    let returnSelf := (e >=s?# mlen_exp) \/# (inf_flag bf) \/# (zero_flag bf) \/# (nan_flag bf) in

    let ext_e := Eunop (Usext 1) e in
    let ext_mlen_exp := Eunop (Usext 1) mlen_exp in
    let round_index := Ebinop Bsub ext_mlen_exp ext_e in 
    let round_index := Eite (round_index <=s?# (zero_exp (unpack_elen+1)))
                        (zero_exp (unpack_elen+1)) 
                        round_index in  (* round_index >= 0 *)
    let unpack_mlen_plus1_exp := Econst(from_Z (unpack_elen+1) (Z.of_nat (unpack_mlen+1))) in
    let round_index := Eite (round_index >=s?# unpack_mlen_plus1_exp)
                        unpack_mlen_plus1_exp
                        round_index in  (* round_index <= unpack_mlen+1 *)
    let round_index_size := unpack_elen + 1 in
    let ext_m := (zero_exp 2) ++# (Eunop (Uzext 2) m) in
    let m_size := unpack_mlen + 4 in
    (* suppose that m_size >= round_pos_size, i.e. unpack_mlen+4 >= unpack_elen+1 *)
    let round_index := Eunop (Uzext (m_size - round_index_size)) round_index in
    let origin_round_pos := Ebinop Bshl (one_exp m_size) round_index in
    let guard_pos := Ebinop Bshl origin_round_pos (one_exp m_size) in
    let round_pos := Ebinop Bshl guard_pos (one_exp m_size) in
    let sticky_mask := Ebinop Bsub guard_pos (one_exp m_size) in
    let is_even := is_all_zeros (Ebinop Band round_pos ext_m) m_size in
    let guard_bit := ~~# (is_all_zeros (Ebinop Band guard_pos ext_m) m_size) in
    let sticky_bit := ~~# (is_all_zeros (Ebinop Band sticky_mask ext_m) m_size) in
    let m_up := roundUp rm s is_even guard_bit sticky_bit in
    let rounded_m := Ebinop Badd ext_m (Eite m_up round_pos (zero_exp m_size)) in
    let mask := Ebinop Bor guard_pos sticky_mask in
    let reverse_mask := Eunop Unot mask in
    let masked_m := Ebinop Band rounded_m reverse_mask in
    (* round_pos is the msb and had rounded up *)
    let top_bit := Eunop (Uextr (m_size-1) (m_size-1)) rounded_m in
    (* round_pos is the leading one or the second bit and had rounded up *)
    let ovf_bit := Eunop (Uextr (m_size-2) (m_size-2)) rounded_m in 
    (* top_bit implies that e <= -2, so e+1 < 0 and then the final result will be 0 or 1, i.e. e=0 *)
    (* ovf_bit implies that e >= -1, when e == -1, the final result will be 0 or 1, i.e. e=0, so ++e is valid
                                     and e >= 0 is the normal aligned case. *)
    let correct_e := Eite (is_Btrue top_bit) (zero_exp unpack_elen)
                      (Eite (is_Btrue ovf_bit) (Ebinop Badd e (one_exp unpack_elen)) e) in
    let extract_m := Eunop (Uextr (unpack_mlen+1) 2) masked_m in
    let correct_m := Ebinop Bor extract_m ((zero_exp (unpack_mlen-1)) ++# (Ebinop Bor top_bit ovf_bit)) in
    let inf_flag := Eite_bexp returnSelf (inf_flag bf) Bfalse in
    let zero_flag := Eite_bexp returnSelf (zero_flag bf)
                      (Eite_bexp (is_all_zeros correct_m unpack_mlen) Btrue Bfalse) in
    let nan_flag := Eite_bexp returnSelf (nan_flag bf) Bfalse in
    let un_s := s in
    let un_e := Eite returnSelf e 
                (Eite zero_flag defaultExponent
                   correct_e) in
    let un_m := Eite returnSelf m
                (Eite zero_flag defaultSignificand
                   correct_m) in
      make_unpackedbf_var gen_var g es te inf_flag zero_flag nan_flag un_s un_e un_m.
      
  Notation unpack := (unpack mlen elen).
  Notation pack := (pack mlen elen).

  Definition roundToIntegral (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (rm : exp) (s e m : exp) : SSATE.env * nat * seq bexp * (exp * exp * exp) :=
    let '(te, g, es, ubf) := unpack gen_var g es te s e m in
    (* let unpack_result := roundToIntegral_unpackbf rm ubf in *)
    let '(te, g, es, unpack_result) := roundToIntegral_unpackbf gen_var g es te rm ubf in
    let repack_result := pack unpack_result in
      (te, g, es, repack_result).
      
End Rti.
