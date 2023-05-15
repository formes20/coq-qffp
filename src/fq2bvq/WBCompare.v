From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From ssrlib Require Import EqVar.
From Coq Require Import ZArith.
From nbits Require Import NBits.
From BitBlasting Require Import Typ TypEnv State.
From BitBlasting Require Import QFBV.
From WordBlasting Require Import WBCommon WBPacking WBClassify.

Import QFBV.
Import QFBVNotation.

Section Compare.

  Variable mlen elen: nat.
  
  Notation unpack_elen := (unpack_elen mlen elen).
  Notation unpack_mlen := (unpack_mlen mlen).
  Notation isNaN_unpackedbf := (isNaN_unpackedbf mlen elen).
  Notation isZero_unpackedbf := (isZero_unpackedbf mlen elen).
  Notation isNegInfinite_unpackedbf := (isNegInfinite_unpackedbf mlen elen).
  Notation isPosInfinite_unpackedbf := (isPosInfinite_unpackedbf mlen elen).
  Notation isSuborNor_unpackedbf := (isSuborNor_unpackedbf mlen elen).
  
(*    (*   ieee754Equal *)
   Definition eq_unpackedbf (mlen elen : nat) (bf1 bf2 : unpackedbf) := 
    let neitherNaN := (~~# (nan_flag bf1)) /\# (~~# (nan_flag bf2)) in
    let bothZero := (zero_flag bf1) /\# (zero_flag bf2) in
    let neitherZero := (~~# (zero_flag bf1)) /\# (~~# (zero_flag bf2)) in
    let flagsAndExponent := neitherNaN /\# 
                            (bothZero \/# (neitherZero /\#
                              ( (Biff (inf_flag bf1) (inf_flag bf2)) /\#
                                (Biff (un_s bf1) (un_s bf2)) /\#
                                ((un_e bf1) =?# (un_e bf2))))) in
      Eite_bexp flagsAndExponent ((un_m bf1) =?# (un_m bf2)) Bfalse. *)

  Definition eq_unpackedbf (mlen elen : nat) (bf1 bf2 : unpackedbf) := 
    let neitherNaN := (~~# (nan_flag bf1)) /\# (~~# (nan_flag bf2)) in
    let bothZero := (zero_flag bf1) /\# (zero_flag bf2) in
    let flagsEqual := (Biff (inf_flag bf1) (inf_flag bf2)) /\#
                      (Biff (zero_flag bf1) (zero_flag bf2)) /\#
                      (Biff (un_s bf1) (un_s bf2)) in
      neitherNaN /\# (bothZero \/# (flagsEqual /\# ((un_e bf1) =?# (un_e bf2)) /\# ((un_m bf1) =?# (un_m bf2)))).

  Definition lt_unpackedbf (bf1 bf2 : unpackedbf) : bexp :=
    let neitherNaN := (~~# (isNaN_unpackedbf bf1)) /\# (~~# (isNaN_unpackedbf  bf2)) in
    let leftZero := (isZero_unpackedbf bf1) /\# (~~# (isZero_unpackedbf bf2)) /\# (~~# (un_s bf2)) in
    let rightZero := (~~# (isZero_unpackedbf bf1)) /\# (isZero_unpackedbf bf2) /\# (un_s bf1) in
    let leftNegInf := (isNegInfinite_unpackedbf bf1) /\# (~~# (isNegInfinite_unpackedbf bf2)) in
    let rightPosInf := (isPosInfinite_unpackedbf bf2) /\# (~~# (isPosInfinite_unpackedbf bf1)) in
    let s1 := un_s bf1 in
    let e1 := un_e bf1 in
    let m1 := un_m bf1 in
    let s2 := un_s bf2 in
    let e2 := un_e bf2 in
    let m2 := un_m bf2 in
    let leftNegRightPos := s1 /\# (~~# s2) in
    let bothNeg := s1 /\# s2 /\# ((e1 >s?# e2) \/# ((e1 =?# e2) /\# (m1 >s?# m2))) in
    let bothPos := (~~# s1) /\# (~~# s2) /\# ((e1 <s?# e2) \/# ((e1 =?# e2) /\# (m1 <s?# m2))) in
    let bothSuborNor := (isSuborNor_unpackedbf bf1) /\# (isSuborNor_unpackedbf bf2) /\# 
                        (leftNegRightPos \/# bothNeg \/# bothPos) in
      neitherNaN /\# (leftZero \/# rightZero \/# leftNegInf \/# rightPosInf \/# bothSuborNor).
  
  Definition le_unpackedbf (bf1 bf2 : unpackedbf) : bexp :=
    (eq_unpackedbf mlen elen bf1 bf2) \/# (lt_unpackedbf bf1 bf2).
  
  Definition gt_unpackedbf (bf1 bf2 : unpackedbf) : bexp := lt_unpackedbf bf2 bf1.
  Definition ge_unpackedbf (bf1 bf2 : unpackedbf) : bexp := le_unpackedbf bf2 bf1.
  
  Definition max_unpackedbf (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (bf1 bf2 : unpackedbf) : SSATE.env * nat * seq bexp * unpackedbf := 
    let returnRight := (isNaN_unpackedbf bf1) \/# (lt_unpackedbf bf1 bf2) in
    let inf_flag := Eite_bexp returnRight (inf_flag bf2) (inf_flag bf1) in
    let zero_flag := Eite_bexp returnRight (zero_flag bf2) (zero_flag bf1) in
    let nan_flag := Eite_bexp returnRight (nan_flag bf2) (nan_flag bf1) in
    let un_s := Eite_bexp returnRight (un_s bf2) (un_s bf1) in
    let un_e := Eite returnRight (un_e bf2) (un_e bf1) in
    let un_m := Eite returnRight (un_m bf2) (un_m bf1) in
    let '(te, g, es, un_e) := make_exp_var gen_var g es te un_e unpack_elen in
    let '(te, g, es, un_m) := make_exp_var gen_var g es te un_m unpack_mlen in
    let result := Build_unpackedbf inf_flag zero_flag nan_flag un_s un_e un_m in
      (te, g, es, result).
      
  Definition min_unpackedbf (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (bf1 bf2 : unpackedbf) : SSATE.env * nat * seq bexp * unpackedbf := 
    let returnLeft := (isNaN_unpackedbf bf2) \/# (lt_unpackedbf bf1 bf2) in
    let inf_flag := Eite_bexp returnLeft (inf_flag bf1) (inf_flag bf2) in
    let zero_flag := Eite_bexp returnLeft (zero_flag bf1) (zero_flag bf2) in
    let nan_flag := Eite_bexp returnLeft (nan_flag bf1) (nan_flag bf2) in
    let un_s := Eite_bexp returnLeft (un_s bf1) (un_s bf2) in
    let un_e := Eite returnLeft (un_e bf1) (un_e bf2) in
    let un_m := Eite returnLeft (un_m bf1) (un_m bf2) in
    let '(te, g, es, un_e) := make_exp_var gen_var g es te un_e unpack_elen in
    let '(te, g, es, un_m) := make_exp_var gen_var g es te un_m unpack_mlen in
    let result := Build_unpackedbf inf_flag zero_flag nan_flag un_s un_e un_m in
      (te, g, es, result).


  Notation unpack := (unpack mlen elen).
  Notation pack := (pack mlen elen).
  
  Definition eq (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (s1 e1 m1 s2 e2 m2 : exp) : SSATE.env * nat * seq bexp * bexp := 
    let '(te, g, es, ubf1) := unpack gen_var g es te s1 e1 m1 in
    let '(te, g, es, ubf2) := unpack gen_var g es te s2 e2 m2 in
      (te, g, es, (eq_unpackedbf mlen elen ubf1 ubf2)).
      
  Definition lt (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (s1 e1 m1 s2 e2 m2 : exp) : SSATE.env * nat * seq bexp * bexp := 
    let '(te, g, es, ubf1) := unpack gen_var g es te s1 e1 m1 in
    let '(te, g, es, ubf2) := unpack gen_var g es te s2 e2 m2 in
      (te, g, es, (lt_unpackedbf ubf1 ubf2)).

  Definition le (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (s1 e1 m1 s2 e2 m2 : exp) : SSATE.env * nat * seq bexp * bexp := 
    let '(te, g, es, ubf1) := unpack gen_var g es te s1 e1 m1 in
    let '(te, g, es, ubf2) := unpack gen_var g es te s2 e2 m2 in
      (te, g, es, (le_unpackedbf ubf1 ubf2)).

  Definition gt (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (s1 e1 m1 s2 e2 m2 : exp) : SSATE.env * nat * seq bexp * bexp := 
    let '(te, g, es, ubf1) := unpack gen_var g es te s1 e1 m1 in
    let '(te, g, es, ubf2) := unpack gen_var g es te s2 e2 m2 in
      (te, g, es, (gt_unpackedbf ubf1 ubf2)).

  Definition ge (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (s1 e1 m1 s2 e2 m2 : exp) : SSATE.env * nat * seq bexp * bexp := 
    let '(te, g, es, ubf1) := unpack gen_var g es te s1 e1 m1 in
    let '(te, g, es, ubf2) := unpack gen_var g es te s2 e2 m2 in
      (te, g, es, (ge_unpackedbf ubf1 ubf2)).
      
  Definition max (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (s1 e1 m1 s2 e2 m2 : exp) : SSATE.env * nat * seq bexp * (exp * exp * exp) := 
    let '(te, g, es, ubf1) := unpack gen_var g es te s1 e1 m1 in
    let '(te, g, es, ubf2) := unpack gen_var g es te s2 e2 m2 in
    let '(te, g, es, unpack_result) := max_unpackedbf gen_var g es te ubf1 ubf2 in
    let repack_result := pack unpack_result in
      (te, g, es, repack_result).
      
  Definition min (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (s1 e1 m1 s2 e2 m2 : exp) : SSATE.env * nat * seq bexp * (exp * exp * exp) := 
    let '(te, g, es, ubf1) := unpack gen_var g es te s1 e1 m1 in
    let '(te, g, es, ubf2) := unpack gen_var g es te s2 e2 m2 in
    let '(te, g, es, unpack_result) := min_unpackedbf gen_var g es te ubf1 ubf2 in
    let repack_result := pack unpack_result in
      (te, g, es, repack_result).
      
End Compare.
