From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From ssrlib Require Import EqVar.
From Coq Require Import ZArith.
From nbits Require Import NBits.
From BitBlasting Require Import Typ TypEnv State.
From BitBlasting Require Import QFBV.
From WordBlasting Require Import WBCommon WBPacking.

Import QFBV.
Import QFBVNotation.

Section Classify.

  Variable mlen elen: nat.
  
  Notation unpack_elen := (unpack_elen mlen elen).
  Notation is_in_normal_range_bexp := (is_in_normal_range_bexp mlen elen).
  Notation is_in_subnormal_range_bexp := (is_in_subnormal_range_bexp mlen elen).

  Definition isInfinite_unpackedbf (mlen elen : nat) (bf : unpackedbf) : bexp := inf_flag bf.
  Definition isZero_unpackedbf (mlen elen : nat) (bf : unpackedbf) : bexp := zero_flag bf.
  Definition isNaN_unpackedbf (mlen elen : nat) (bf : unpackedbf) : bexp := nan_flag bf.
  
  Definition isNormal_unpackedbf (bf : unpackedbf) : bexp := 
    (~~# inf_flag bf) /\# (~~# zero_flag bf) /\# (~~# nan_flag bf) /\# 
    (is_in_normal_range_bexp (un_e bf) unpack_elen).
    
  Definition isSubNormal_unpackedbf (bf : unpackedbf) : bexp := 
    (~~# inf_flag bf) /\# (~~# zero_flag bf) /\# (~~# nan_flag bf) /\# 
    (is_in_subnormal_range_bexp (un_e bf) unpack_elen).
    
  Definition isPositive_unpackedbf (mlen elen : nat) (bf : unpackedbf) : bexp :=
    (~~# (nan_flag bf)) /\# (~~# (un_s bf)).
    
  Definition isNegative_unpackedbf (mlen elen : nat) (bf : unpackedbf) : bexp :=
    (~~# (nan_flag bf)) /\# (un_s bf).
  
  Definition isPosInfinite_unpackedbf (bf : unpackedbf) : bexp := 
    (isInfinite_unpackedbf mlen elen bf) /\# (~~# (un_s bf)).
    
  Definition isNegInfinite_unpackedbf (bf : unpackedbf) : bexp := 
    (isInfinite_unpackedbf mlen elen bf) /\# (un_s bf).
  
  Definition isSuborNor_unpackedbf (bf : unpackedbf) : bexp := (isNormal_unpackedbf bf) \/# (isSubNormal_unpackedbf bf).
  
  
  Notation unpack := (unpack mlen elen).
   (* SMT-LIB interfaces *)
  Definition isZero (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (s e m : exp) : SSATE.env * nat * seq bexp * bexp := 
    let '(te, g, es, ubf) := unpack gen_var g es te s e m in
      (te, g, es, (isZero_unpackedbf mlen elen ubf)).
      
  Definition isNormal (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (s e m : exp) : SSATE.env * nat * seq bexp * bexp := 
    let '(te, g, es, ubf) := unpack gen_var g es te s e m in
      (te, g, es, (isNormal_unpackedbf ubf)).
      
  Definition isSubNormal (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (s e m : exp) : SSATE.env * nat * seq bexp * bexp := 
    let '(te, g, es, ubf) := unpack gen_var g es te s e m in
      (te, g, es, (isSubNormal_unpackedbf ubf)).
      
  Definition isInfinite (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env)  (s e m : exp) : SSATE.env * nat * seq bexp * bexp := 
    let '(te, g, es, ubf) := unpack gen_var g es te s e m in
      (te, g, es, (isInfinite_unpackedbf mlen elen ubf)).
      
  Definition isNaN (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (s e m : exp) : SSATE.env * nat * seq bexp * bexp := 
    let '(te, g, es, ubf) := unpack gen_var g es te s e m in
      (te, g, es, (isNaN_unpackedbf mlen elen ubf)).
      
  Definition isPositive (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (s e m : exp) : SSATE.env * nat * seq bexp * bexp := 
    let '(te, g, es, ubf) := unpack gen_var g es te s e m in
      (te, g, es, (isPositive_unpackedbf mlen elen ubf)).
      
  Definition isNegative (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (s e m : exp) : SSATE.env * nat * seq bexp * bexp := 
    let '(te, g, es, ubf) := unpack gen_var g es te s e m in
      (te, g, es, (isNegative_unpackedbf mlen elen ubf)).

End Classify.
