From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From ssrlib Require Import EqVar.
From Coq Require Import ZArith.
From nbits Require Import NBits.
From BitBlasting Require Import Typ TypEnv State.
From BitBlasting Require Import QFBV.
From WordBlasting Require Import WBCommon WBPacking.

Import QFBV.
Import QFBVNotation.

Section AbsNeg.

  Variable mlen elen: nat.
  
  Notation unpack_elen := (unpack_elen mlen elen).
  Notation unpack_mlen := (unpack_mlen mlen).
  Notation defaultExponent := (defaultExponent mlen elen).
  Notation defaultSignificand := (defaultSignificand mlen).

  Definition abs_unpackedbf (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env)  (bf : unpackedbf) : SSATE.env * nat * seq bexp * unpackedbf := 
    let inf_flag := Eite_bexp (nan_flag bf) Bfalse (inf_flag bf) in
    let zero_flag := Eite_bexp (nan_flag bf) Bfalse (zero_flag bf)  in
    let un_s := Eite_bexp (nan_flag bf) Btrue Bfalse in
    let un_e := Eite (nan_flag bf) defaultExponent (un_e bf) in
    let un_m := Eite (nan_flag bf) defaultSignificand (un_m bf) in
    let '(te, g, es, un_e) := make_exp_var gen_var g es te un_e unpack_elen in
    let '(te, g, es, un_m) := make_exp_var gen_var g es te un_m unpack_mlen in
    let result := Build_unpackedbf inf_flag zero_flag (nan_flag bf) un_s un_e un_m in
      (te, g, es, result).
  
  Definition neg_unpackedbf (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env)  (bf : unpackedbf) : SSATE.env * nat * seq bexp * unpackedbf := 
    let inf_flag := Eite_bexp (nan_flag bf) Bfalse (inf_flag bf) in
    let zero_flag := Eite_bexp (nan_flag bf) Bfalse (zero_flag bf)  in
    let un_s := Eite_bexp (nan_flag bf) Btrue (~~# (un_s bf)) in
    let un_e := Eite (nan_flag bf) defaultExponent (un_e bf) in
    let un_m := Eite (nan_flag bf) defaultSignificand (un_m bf) in
    let '(te, g, es, un_e) := make_exp_var gen_var g es te un_e unpack_elen in
    let '(te, g, es, un_m) := make_exp_var gen_var g es te un_m unpack_mlen in
    let result := Build_unpackedbf inf_flag zero_flag (nan_flag bf) un_s un_e un_m in
      (te, g, es, result).
  
  Notation unpack := (unpack mlen elen).
  Notation pack := (pack mlen elen).
  
  Definition abs (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (s e m : exp) : SSATE.env * nat * seq bexp * (exp * exp * exp) := 
    let '(te, g, es, ubf) := unpack gen_var g es te s e m in
    let '(te, g, es, unpack_result) := abs_unpackedbf gen_var g es te ubf in
    let repack_result := pack unpack_result in
      (te, g, es, repack_result).
      
  Definition neg (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (s e m : exp) : SSATE.env * nat * seq bexp * (exp * exp * exp) := 
    let '(te, g, es, ubf) := unpack gen_var g es te s e m in
    let '(te, g, es, unpack_result) := neg_unpackedbf gen_var g es te ubf in
    let repack_result := pack unpack_result in
      (te, g, es, repack_result).

End AbsNeg.
