From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From BitBlasting Require Import Typ TypEnv State.
From BitBlasting Require Import QFBV.
From nbits Require Import NBits.
From ssrlib Require Import EqVar.
From BitBlasting Require Import BBCommon.

Import QFBV.

Module QFBVNotation.
  Notation "b1 /\# b2" := (Bconj b1 b2) (at level 40, left associativity).
  Notation "b1 \/# b2" := (Bdisj b1 b2) (at level 40, left associativity).
  Notation "~~# b" := (Blneg b) (at level 35, right associativity).
  Notation "bs1 =?# bs2" := (Bbinop Beq bs1 bs2) (at level 70, no associativity).
  Notation "bs1 <u?# bs2" := (Bbinop Bult bs1 bs2) (at level 70, no associativity).
  Notation "bs1 >u?# bs2" := (Bbinop Bugt bs1 bs2) (at level 70, no associativity).
  Notation "bs1 <=u?# bs2" := (Bbinop Bule bs1 bs2) (at level 70, no associativity).
  Notation "bs1 >=u?# bs2" := (Bbinop Buge bs1 bs2) (at level 70, no associativity).
  Notation "bs1 <s?# bs2" := (Bbinop Bslt bs1 bs2) (at level 70, no associativity).
  Notation "bs1 >s?# bs2" := (Bbinop Bsgt bs1 bs2) (at level 70, no associativity).
  Notation "bs1 <=s?# bs2" := (Bbinop Bsle bs1 bs2) (at level 70, no associativity).
  Notation "bs1 >=s?# bs2" := (Bbinop Bsge bs1 bs2) (at level 70, no associativity).
  Notation "bs1 ++# bs2" := (Ebinop Bconcat bs2 bs1) (at level 65, no associativity).
End QFBVNotation.

Import QFBVNotation.

Section IntroVar.

(* Function of generating variable passed by Ocaml *)
Variable gen_var : nat -> (ssavar * nat).

(* Variable ID *)
Variable g : nat.

(* Boolean expressions in the top level *)
Variable es : seq bexp.

(* a map from a variable to its type *)
Variable te : SSATE.env.

Definition make_exp_var (target : exp) (bs_size : nat)  : SSATE.env * nat * seq bexp * exp :=
  let ty := Tuint bs_size in
  let (v, g') := gen_var g in
  let te' := SSATE.add v ty te in
  let var_exp := Evar v in
  let eq_bexp := Bbinop Beq var_exp target in
  let es' := eq_bexp ::es in
    (te', g', es', var_exp).
    
Definition make_Evar (bs_size : nat) : SSATE.env * nat * seq bexp * exp :=
  let ty := Tuint bs_size in
  let (v, g') := gen_var g in
  let te' := SSATE.add v ty te in
  let var_exp := Evar v in
    (te', g', es, var_exp).

(* FIXME : opti *)
Definition make_bexp_var (target : bexp) : SSATE.env * nat * seq bexp * bexp :=
  let ty := Tuint 1 in
  let (v, g') := gen_var g in
  let te' := SSATE.add v ty te in
  let var_exp := Evar v in
  let target_exp := Eite target (Econst [::true]) (Econst [::false]) in
  let eq_bexp := Bbinop Beq var_exp target_exp in
  let bs' := eq_bexp ::es in
    (te', g', bs', (Bbinop Beq var_exp (Econst [::true]))).

End IntroVar.

Section Utils.

  Definition msb_bexp (bs : exp) : bexp := Bbinop Beq (Eunop (Uhigh 1) bs) (Econst [::true]).
  Definition lsb_bexp (bs : exp) : bexp := Bbinop Beq (Eunop (Ulow 1) bs) (Econst [::true]).
  Definition has_leading_one (bs : exp) : bexp := msb_bexp bs. 
  
  Definition zero_exp (n : nat) := Econst (zeros n).
  Definition ones_exp (n : nat) := Econst (ones n).
  Definition one_exp (n : nat) := Econst ([::true] ++ zeros (n-1)).
  
  Definition is_all_zeros (bs : exp) (bs_size : nat) : bexp :=
    Bbinop Beq bs (zero_exp bs_size).
  Definition is_all_ones (bs : exp) (bs_size : nat) : bexp :=
    Bbinop Beq bs (ones_exp bs_size).
    
  Definition Btrue_exp := Econst [::true].
  Definition Bfalse_exp := Econst [::false].
  
  Definition is_Btrue (e : exp) : bexp := Bbinop Beq e Btrue_exp. 

  Definition bexp_exp (b : bexp) : exp :=
    Eite b (Econst [::true]) (Econst [::false]).
    
  Definition Eite_bexp (cond b1 b2 : bexp) : bexp :=
    (cond /\# b1) \/# ((~~# cond) /\# b2).
    
  Definition Bimp b1 b2 := Bdisj (Blneg b1) b2.
  Definition Biff b1 b2 := Bconj (Bimp b1 b2) (Bimp b2 b1).

  Definition Bsucc (bs : exp) (bs_size : nat) : exp * bexp :=
    let succ_bs := Ebinop Badd bs (one_exp bs_size) in
    let is_ovf := Bbinop Buaddo bs (one_exp bs_size) in
      (succ_bs, is_ovf).
      
  Definition Bxor_bexp (b1 b2 : bexp) : bexp := 
    ((~~# b1) /\# b2) \/# (b1 /\# (~~# b2)).
    
  Definition Badc (c : bexp) (bs1 bs2 : exp) (bs_size : nat) : exp := 
    let sum_bs := Ebinop Badd bs1 bs2 in 
    let carry := Eite c (one_exp bs_size) (zero_exp bs_size) in
    let sum_bs_carry := Ebinop Badd sum_bs carry in
      sum_bs_carry.
        
End Utils.

Section ieee754fp.

  Variable mlen elen: nat.
  
  Definition s_bexp (bf : exp) : bexp := msb_bexp bf.
  Definition s_exp (bf : exp) : exp := Eunop (Uextr (elen+mlen) (elen+mlen)) bf.
  Definition e_exp (bf : exp) : exp := Eunop (Uextr (elen-1+mlen) (mlen)) bf.
  Definition m_exp (bf : exp) : exp := Eunop (Uextr (mlen-1) 0) bf.
  
  Definition is_e_zero (bf : exp) : bexp := 
    Bbinop Beq ((e_exp bf)) (zero_exp elen). 
  
  Definition is_e_all_one (bf : exp) : bexp := 
    Bbinop Beq ((e_exp bf)) (ones_exp elen).
  
  Definition is_m_zero (bf : exp) : bexp := 
    Bbinop Beq ((m_exp bf)) (zero_exp mlen).
  
  (* const *)
  Definition fp_NaN : exp := Econst (ones (mlen+elen+1)).  (* default value is all one *)
  Definition pos_infinity :=  Econst ((zeros mlen) ++ (ones elen) ++ [::false]).
  Definition neg_infinity :=  Econst ((zeros mlen) ++ (ones elen) ++ [::true]).
  Definition pos_zero : exp := Econst (zeros (mlen) ++ zeros (elen) ++ [::false]).
  Definition neg_zero : exp := Econst (zeros (mlen) ++ zeros (elen) ++ [::true]).
  
  (* for extracting code *)
  Definition fp_spec_val := (fp_NaN, pos_infinity, neg_infinity, pos_zero, neg_zero).

(*   (* Classification *)
  Definition isZero (bf : exp) : bexp := (is_m_zero bf) /\# (is_e_zero bf).
  Definition isNormal (bf : exp) : bexp := ~~#(is_e_all_one bf) /\# ~~#(is_e_zero bf).
  Definition isSubNormal (bf : exp) : bexp := (is_e_zero bf) /\# ~~#(is_m_zero bf).
  Definition isInfinite (bf : exp) : bexp :=  (is_e_all_one bf) /\# (is_m_zero bf).
  Definition isNaN (bf : exp) : bexp := (is_e_all_one bf) /\# ~~#(is_m_zero bf).
  
  Definition isPosInfinite (bf : exp) : bexp := (isInfinite bf) /\# (~~# s_bexp bf).
  Definition isNegInfinite (bf : exp) : bexp := (isInfinite bf) /\# (s_bexp bf).
  Definition isPosZero (bf : exp) : bexp := (isZero bf) /\# (~~# s_bexp bf).
  Definition isNegZero (bf : exp) : bexp := (isZero bf) /\# (s_bexp bf).
  Definition isSuborNor (bf : exp) : bexp := (isNormal bf) \/# (isSubNormal bf).
  
  Definition isPositive (bf : exp) : bexp := ~~#(isNaN bf) /\# ~~#(s_bexp bf).
  Definition isNegative (bf : exp) : bexp := ~~#(isNaN bf) /\# (s_bexp bf).
  
  (* Comparision *)
  Definition eq (bf1 bf2 : exp) := (~~# (isNaN bf1)) /\# (~~# (isNaN bf2)) /\#  
                                   ( ((isZero bf1) /\# (isZero bf2)) \/#
                                     (bf1 =?# bf2) ).
  Definition lt (bf1 bf2 : exp) : bexp :=
    let bothNotNaN := (~~# (isNaN bf1)) /\# (~~# (isNaN bf2)) in
    let leftZero := (isZero bf1) /\# (~~# (isZero bf2)) /\# (~~# (s_bexp bf2)) in
    let rightZero := (~~# (isZero bf1)) /\# (isZero bf2) /\# (s_bexp bf1) in
    let leftNegInf := isNegInfinite bf1 /\# (~~# (isNegInfinite bf2)) in
    let rightPosInf := isPosInfinite bf2 /\# (~~# (isPosInfinite bf1)) in
    let s1 := s_bexp bf1 in
    let e1 := e_exp bf1 in
    let m1 := m_exp bf1 in
    let s2 := s_bexp bf2 in
    let e2 := e_exp bf2 in
    let m2 := m_exp bf2 in
    let leftNegRightPos := s1 /\# (~~# s2) in
    let bothNeg := s1 /\# s2 /\# ((e1 >u?# e2) \/# ((e1 =?# e2) /\# (m1 >u?# m2))) in
    let bothPos := (~~# s1) /\# (~~# s2) /\# ((e1 <u?# e2) \/# ((e1 =?# e2) /\# (m1 <u?# m2))) in
    let bothSuborNor := isSuborNor bf1 /\# isSuborNor bf2 /\# (leftNegRightPos \/# bothNeg \/# bothPos) in
      bothNotNaN /\# (leftZero \/# rightZero \/# leftNegInf \/# rightPosInf \/# bothSuborNor).
  
  Definition le (bf1 bf2 : exp) : bexp :=
    let bothNotNaN := (~~# (isNaN bf1)) /\# (~~# (isNaN bf2)) in
    let exact := bf1 =?# bf2 in
    let bothZero := (isZero bf1) /\# (isZero bf2) in
    let leftZero := (isZero bf1) /\# (~~# (isZero bf2)) /\# (~~# (s_bexp bf2)) in
    let rightZero := (~~# (isZero bf1)) /\# (isZero bf2) /\# (s_bexp bf1) in
    let leftNegInf := isNegInfinite bf1 /\# (~~# (isNegInfinite bf2)) in
    let rightPosInf := isPosInfinite bf2 /\# (~~# (isPosInfinite bf1)) in
    let s1 := s_bexp bf1 in
    let e1 := e_exp bf1 in
    let m1 := m_exp bf1 in
    let s2 := s_bexp bf2 in
    let e2 := e_exp bf2 in
    let m2 := m_exp bf2 in
    let leftNegRightPos := s1 /\# (~~# s2) in
    let bothNeg := s1 /\# s2 /\# ((e1 >u?# e2) \/# ((e1 =?# e2) /\# (m1 >u?# m2))) in
    let bothPos := (~~# s1) /\# (~~# s2) /\# ((e1 <u?# e2) \/# ((e1 =?# e2) /\# (m1 <u?# m2))) in
    let bothSuborNor := isSuborNor bf1 /\# isSuborNor bf2 /\# (leftNegRightPos \/# bothNeg \/# bothPos) in
      bothNotNaN /\# (exact \/# bothZero \/# leftZero \/# rightZero \/# leftNegInf \/# rightPosInf \/# bothSuborNor).
  
  Definition gt (bf1 bf2 : exp) : bexp := lt bf2 bf1.
  Definition ge (bf1 bf2 : exp) : bexp := le bf2 bf1.
  
  Definition max (bf1 bf2 : exp) : exp := Eite ((isNaN bf1) \/# (lt bf1 bf2)) bf2 bf1.
  Definition min (bf1 bf2 : exp) : exp := Eite ((isNaN bf2) \/# (lt bf1 bf2)) bf1 bf2.
  
  (* unary op *)
  Definition abs (bf : exp) : exp := 
    Eite (isNaN bf) fp_NaN (Ebinop Band bf (Econst(ones(mlen+elen) ++ [::false]))).
  
  Definition neg (bf : exp) : exp := 
    Eite (isNaN bf) fp_NaN (Ebinop Bxor bf (Econst(zeros(mlen+elen) ++ [::true]))). *)

End ieee754fp.
