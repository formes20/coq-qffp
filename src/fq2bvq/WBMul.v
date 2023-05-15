From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From ssrlib Require Import EqVar.
From Coq Require Import ZArith.
From nbits Require Import NBits.
From BitBlasting Require Import Typ TypEnv State.
From BitBlasting Require Import QFBV.
From WordBlasting Require Import WBCommon WBPacking WBRounding.

Import QFBV.
Import QFBVNotation.

Section Mul.

  Variable mlen elen: nat.
  
  Notation unpack_elen := (unpack_elen mlen elen).
  Notation unpack_mlen := (unpack_mlen mlen).
  Notation defaultExponent := (defaultExponent mlen elen).
  Notation defaultSignificand := (defaultSignificand mlen).
  Notation round := (round mlen elen).
  Notation make_unpackedbf_var := ( make_unpackedbf_var mlen elen).
  
  Definition xorSign (s1 s2 : bexp) : bexp := Bxor_bexp s1 s2.

  Definition mul_unpackbf (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env)  (rm : exp) (bf1 bf2 : unpackedbf) : SSATE.env * nat * seq bexp * unpackedbf :=
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
    let rounded_result := round rm s returnZero s sum_e normal_product_m e_size m_size in
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
                  (Eite_bexp (returnInf \/# returnZero) s (un_s rounded_result)) in
    let un_e := Eite (returnNaN \/# returnInf \/# returnZero) defaultExponent
                  (un_e rounded_result) in
    let un_m := Eite (returnNaN \/# returnInf \/# returnZero) defaultSignificand
                  (un_m rounded_result) in
       make_unpackedbf_var gen_var g es te inf_flag zero_flag nan_flag un_s un_e un_m.
  
  Notation unpack := (unpack mlen elen).
  Notation pack := (pack mlen elen).
  
   Definition mul (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (rm : exp) (s1 e1 m1 s2 e2 m2 : exp) : SSATE.env * nat * seq bexp * (exp * exp * exp) :=
    let '(te, g, es, ubf1) := unpack gen_var g es te s1 e1 m1 in
    let '(te, g, es, ubf2) := unpack gen_var g es te s2 e2 m2 in
    let '(te, g, es, unpack_result) := mul_unpackbf gen_var g es te rm ubf1 ubf2 in
    let repack_result := pack unpack_result in
      (te, g, es, repack_result).
      
End Mul.
