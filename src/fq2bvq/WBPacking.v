From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From ssrlib Require Import EqVar.
From Coq Require Import ZArith.
From nbits Require Import NBits.
From BitBlasting Require Import Typ TypEnv State.
From BitBlasting Require Import QFBV.
From WordBlasting Require Import WBCommon.

Import QFBV.
Import QFBVNotation.

Section Packing.

  Variable mlen elen: nat.

  Definition mlen_Z:Z := Z.of_nat mlen.
  Definition elen_Z:Z := Z.of_nat elen.
  
  Definition unpack_mlen := mlen+1.
  Definition unpack_mlen_Z : Z := Z.of_nat unpack_mlen.

  Definition bias : Z := 2^(elen_Z-1)-1.    
  
  Definition max_normal_e : Z := bias.
  Definition min_normal_e : Z := -(bias-1).
  Definition max_subnormal_e: Z := -bias.
  Definition min_subnormal_e: Z := max_subnormal_e-(unpack_mlen_Z-2).
  
  (* unpack_elen >= elen *)
  Definition unpack_elen_Z : Z := Z.log2_up (Z.abs min_subnormal_e) + 1.
  Definition unpack_elen := Z.to_nat unpack_elen_Z.

  Definition bias_exp : exp := Econst (from_Z unpack_elen bias).
  Definition max_normal_e_exp : exp := Econst (from_Z unpack_elen max_normal_e).
  Definition min_normal_e_exp : exp := Econst (from_Z unpack_elen min_normal_e).
  Definition max_subnormal_e_exp: exp := Econst (from_Z unpack_elen max_subnormal_e).
  Definition min_subnormal_e_exp: exp := Econst (from_Z unpack_elen min_subnormal_e).
  Definition max_signficand_exp : exp := ones_exp unpack_mlen.
  Definition min_signficand_exp : exp := Econst ((zeros (unpack_mlen-1) ++ [::true])).

  Definition is_in_normal_range_bexp (e : exp) (e_size : nat) : bexp :=
    let max_normal_e_exp_ext := Eunop (Usext (e_size - unpack_elen)) max_normal_e_exp in
    let min_normal_e_exp_ext := Eunop (Usext (e_size - unpack_elen)) min_normal_e_exp in
    (min_normal_e_exp_ext <=s?# e) /\# (e <=s?# max_normal_e_exp_ext).
  
  Definition is_in_subnormal_range_bexp (e : exp) (e_size : nat) : bexp :=
    let max_subnormal_e_exp_ext := Eunop (Usext (e_size - unpack_elen)) max_subnormal_e_exp in
    let min_subnormal_e_exp_ext := Eunop (Usext (e_size - unpack_elen)) min_subnormal_e_exp in
    (min_subnormal_e_exp_ext <=s?# e) /\# (e <=s?# max_subnormal_e_exp_ext).
    
  Definition is_overflow_bexp (e : exp) (e_size : nat) : bexp := 
    let max_normal_e_exp_ext := Eunop (Usext (e_size - unpack_elen)) max_normal_e_exp in
      e >s?# max_normal_e_exp_ext.
  
  Definition is_underflow_bexp (e : exp) (e_size : nat): bexp := 
    let min_subnormal_e_exp_ext := Eunop (Usext (e_size - unpack_elen)) min_subnormal_e_exp in
      e <s?# min_subnormal_e_exp_ext.
 
  
  Record unpackedbf :={ inf_flag : bexp; zero_flag : bexp ; nan_flag : bexp ;
                        un_s : bexp ; un_e : exp; un_m : exp }.
    
  Definition unpackedbf_of_exp (bs : exp) : unpackedbf :=
    let inf_flag := is_Btrue (Eunop (Uextr (unpack_elen+unpack_mlen+3) (unpack_elen+unpack_mlen+3)) bs) in
    let zero_flag := is_Btrue (Eunop (Uextr (unpack_elen+unpack_mlen+2) (unpack_elen+unpack_mlen+2)) bs) in
    let nan_flag := is_Btrue (Eunop (Uextr (unpack_elen+unpack_mlen+1) (unpack_elen+unpack_mlen+1)) bs) in
    let un_s := is_Btrue (Eunop (Uextr (unpack_elen+unpack_mlen) (unpack_elen+unpack_mlen)) bs) in
    let un_e := Eunop (Uextr (unpack_elen+unpack_mlen-1) (unpack_mlen)) bs in
    let un_m := Eunop (Uextr (unpack_mlen-1) 0) bs in
      Build_unpackedbf inf_flag zero_flag nan_flag un_s un_e un_m.
  
  Definition exp_of_unpackedbf (bf : unpackedbf) : exp :=
    let inf_flag_exp := bexp_exp (inf_flag bf) in
    let zero_flag_exp := bexp_exp (zero_flag bf) in
    let nan_flag_exp := bexp_exp (nan_flag bf) in
    let un_s_exp := bexp_exp (un_s bf) in
      (un_m bf) ++# (un_e bf) ++# un_s_exp ++# nan_flag_exp ++# zero_flag_exp ++# inf_flag_exp.
      
  Definition make_unpackedbf_var (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (inf_flag zero_flag nan_flag un_s : bexp) (un_e un_m : exp) : SSATE.env * nat * seq bexp * unpackedbf :=
    let '(te, g, es, inf_flag) := make_bexp_var gen_var g es te inf_flag in
    let '(te, g, es, zero_flag) := make_bexp_var gen_var g es te zero_flag in
    let '(te, g, es, nan_flag) := make_bexp_var gen_var g es te nan_flag in
    let '(te, g, es, un_s) := make_bexp_var gen_var g es te un_s in
    let '(te, g, es, un_e) := make_exp_var gen_var g es te un_e unpack_elen in
    let '(te, g, es, un_m) := make_exp_var gen_var g es te un_m unpack_mlen in
    let result := Build_unpackedbf inf_flag zero_flag nan_flag un_s un_e un_m in
      (te, g, es, result).
      
  Definition make_ext_unpackedbf_var (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (inf_flag zero_flag nan_flag un_s : bexp) (un_e un_m : exp) (e_size m_size : nat) : SSATE.env * nat * seq bexp * unpackedbf :=
    let '(te, g, es, inf_flag) := make_bexp_var gen_var g es te inf_flag in
    let '(te, g, es, zero_flag) := make_bexp_var gen_var g es te zero_flag in
    let '(te, g, es, nan_flag) := make_bexp_var gen_var g es te nan_flag in
    let '(te, g, es, un_s) := make_bexp_var gen_var g es te un_s in
    let '(te, g, es, un_e) := make_exp_var gen_var g es te un_e e_size in
    let '(te, g, es, un_m) := make_exp_var gen_var g es te un_m m_size in
    let result := Build_unpackedbf inf_flag zero_flag nan_flag un_s un_e un_m in
      (te, g, es, result).
  
  Definition defaultExponent := Econst (zeros unpack_elen).
  Definition defaultExponent_ext (e_size : nat) := Econst (zeros e_size).
  Definition defaultSignificand := Econst (zeros (unpack_mlen-1) ++ [::true]).
  Definition defaultSignificand_ext (m_size : nat) := Econst (zeros (m_size-1) ++ [::true]).
  
  Definition unpack_infinity (un_s : bexp) := 
    let inf_flag := Btrue in
    let zero_flag := Bfalse in
    let nan_flag := Bfalse in
    let un_e := defaultExponent in
    let un_m := defaultSignificand in
      Build_unpackedbf inf_flag zero_flag nan_flag un_s un_e un_m.
      
  Definition unpack_zero (un_s : bexp) := 
    let inf_flag := Bfalse in
    let zero_flag := Btrue in
    let nan_flag := Bfalse in
    let un_e := defaultExponent in
    let un_m := defaultSignificand in
      Build_unpackedbf inf_flag zero_flag nan_flag un_s un_e un_m.
      
  (* sign of nan is negetive (according to SMTLIB) *)
  Definition unpack_NaN : unpackedbf :=
    let inf_flag := Bfalse in
    let zero_flag := Bfalse in
    let nan_flag := Btrue in
    let un_s := Btrue in
    let un_e := defaultExponent in
    let un_m := defaultSignificand in
      Build_unpackedbf inf_flag zero_flag nan_flag un_s un_e un_m.
  
(*     (* For simplicity, not efficiency *)
  Fixpoint normalize_loop (e m : exp) (iter : nat) : exp * exp :=  
    match iter with
      | 0 => (e, m)
      | S iter' => let ls_m := Ebinop Bshl m (one_exp unpack_mlen) in 
                   let dec_e := Ebinop Bsub e (one_exp unpack_elen) in 
                   let next_m := Eite (msb_bexp m) m ls_m in
                   let next_e := Eite (msb_bexp m) e dec_e in
                    normalize_loop next_e next_m iter'
    end. 
 
  Definition normalize (e m : exp) := normalize_loop e m unpack_mlen. *)
  
  Fixpoint normalize_shift_amount (e m : exp) (shift_amount : exp) (m_size : nat) (iter : nat) : exp :=  
    match iter with
      | 0 => shift_amount
      | S iter' => let ls_m := Ebinop Bshl m shift_amount in 
                   (* for wellform *)
                   let next_shift_amount := Ebinop Badd shift_amount (one_exp m_size) in
                   let has_leading_one := msb_bexp ls_m in
                     Eite has_leading_one shift_amount (normalize_shift_amount e m next_shift_amount m_size iter') 
    end. 
    
  Fixpoint normalize_shift_amount_old (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (e m : exp) (shift_amount : exp) (m_size : nat) (iter : nat) : SSATE.env * nat * seq bexp * exp :=  
    match iter with
      | 0 => (te, g, es, shift_amount)
      | S iter' => let ls_m := Ebinop Bshl m shift_amount in
                   let '(te, g, es, ls_m) := make_exp_var gen_var g es te ls_m m_size in
                   let next_shift_amount := Ebinop Badd shift_amount (one_exp m_size) in 
                   let '(te, g, es, next_shift_amount) := make_exp_var gen_var g es te next_shift_amount m_size in
                   let has_leading_one := msb_bexp ls_m in
                   let '(te, g, es, next_run) := normalize_shift_amount_old gen_var g es te e m next_shift_amount m_size iter' in
                      make_exp_var gen_var g es te (Eite has_leading_one shift_amount next_run) m_size
    end. 
  
  Definition normalize_shift_amount_sat (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (m : exp) (m_size : nat) : SSATE.env * nat * seq bexp * exp :=
    let isZero := is_all_zeros m m_size in
    let '(te, g, es, shift_amount) := make_Evar gen_var g es te m_size in
    let range_limit := (shift_amount >=u?# (zero_exp m_size)) /\# (shift_amount <u?# (Econst (from_nat m_size m_size))) in
    let leading_one := msb_bexp (Ebinop Bshl m shift_amount) in
    let init_mask := ones_exp m_size in
    let shifted_mask := Ebinop Blshr init_mask shift_amount in
    let mask := Eunop Unot shifted_mask in
    let leading_zeros := (Ebinop Band mask m) =?# (zero_exp m_size) in
    let limits := isZero \/# (range_limit /\# leading_one /\# leading_zeros) in
    let es := limits :: es in
      (te, g, es, shift_amount).
      
 Definition normalize_old (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (e m : exp) (e_size m_size : nat) : SSATE.env * nat * seq bexp * exp * exp :=
    let init_shift_amount := zero_exp m_size in
    let '(te, g, es, shift_amount) := normalize_shift_amount_old gen_var g es te e m init_shift_amount m_size (m_size-1) in
    let normal_m := Ebinop Bshl m shift_amount in
    let e_shift_amount := Eunop (Uextr (e_size-1) 0) shift_amount in
    let normal_e := Ebinop Bsub e e_shift_amount in
    let '(te, g, es, normal_m_v) := make_exp_var gen_var g es te normal_m m_size in
    let '(te, g, es, normal_e_v) := make_exp_var gen_var g es te normal_e e_size in 
      (te, g, es, normal_e_v, normal_m_v).  
      
 Definition normalize_sat (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (e m : exp) (e_size m_size : nat) : SSATE.env * nat * seq bexp * exp * exp :=
    let '(te, g, es, shift_amount) := normalize_shift_amount_sat gen_var g es te m m_size in 
    let normal_m := Ebinop Bshl m shift_amount in
    let e_shift_amount := Eunop (Uextr (e_size-1) 0) shift_amount in
    let normal_e := Ebinop Bsub e e_shift_amount in
      (te, g, es, normal_e, normal_m).
      
  Fixpoint normalize_shift_amount_bin (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (m : exp) (shift_amount : exp) (m_size : nat) (deactiveShifts : bexp) (iter : nat) : SSATE.env * nat * seq bexp * exp :=  
    match iter with
      | 0 => (te, g, es, shift_amount)
      | S iter' => let deactiveShifts := deactiveShifts \/# (msb_bexp m) in
                   let shift_amount_nat := Z.to_nat (Z.pow 2 ((Z.of_nat iter)-1)) in
                   let mask := (zero_exp (m_size - shift_amount_nat)) ++# (ones_exp shift_amount_nat) in
                   let shiftNeeded := (~~# deactiveShifts) /\#
                                      (is_all_zeros (Ebinop Band mask m) m_size) in
                   let shifted := Eite shiftNeeded (Ebinop Bshl m (Econst (from_nat m_size shift_amount_nat))) m in
                   let shift_amount := Eite shiftNeeded (Ebinop Bor shift_amount (Econst (from_nat m_size shift_amount_nat))) shift_amount in
                   let '(te, g, es, shifted) := make_exp_var gen_var g es te shifted m_size in
                   let '(te, g, es, shift_amount) := make_exp_var gen_var g es te shift_amount m_size in
                   let '(te, g, es, deactiveShifts) := make_bexp_var gen_var g es te deactiveShifts in
                     normalize_shift_amount_bin gen_var g es te shifted shift_amount m_size deactiveShifts iter'
    end. 
    
 Definition normalize_bin (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (e m : exp) (e_size m_size : nat) : SSATE.env * nat * seq bexp * exp * exp :=
    let init_shift_amount := zero_exp m_size in
    let init_iter := (Z.to_nat (Z.log2_up (Z.of_nat m_size))) in
    let zero_case := is_all_zeros m m_size in
    let '(te, g, es, shift_amount) := normalize_shift_amount_bin gen_var g es te m init_shift_amount m_size zero_case init_iter in 
    let normal_m := Ebinop Bshl m shift_amount in
    let e_shift_amount := Eunop (Uextr (e_size-1) 0) shift_amount in
    let normal_e := Ebinop Bsub e e_shift_amount in
      (te, g, es, normal_e, normal_m).  
      
  Definition normalize := normalize_sat.

  Definition unpack (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (s e m : exp) : SSATE.env * nat * seq bexp * unpackedbf :=
    let returnInf := (is_all_ones e elen) /\# (is_all_zeros m mlen) in
    let returnZero := (is_all_zeros e elen) /\# (is_all_zeros m mlen) in
    let returnNormal := (~~# (is_all_zeros e elen)) /\# (~~# (is_all_ones e elen)) in
    let returnNaN := (is_all_ones e elen) /\# (~~# (is_all_zeros m mlen)) in
    let extended_e := Eunop (Uzext (unpack_elen - elen)) e in
    let nor_m := m ++# (Econst [::true]) in
    let nor_e := Ebinop Bsub extended_e (Econst (from_Z unpack_elen bias)) in
    let subnor_m_base := m ++# (Econst [::false]) in
    let subnor_e_base := min_normal_e_exp in
    let '(te, g, es, subnor_e, subnor_m) := normalize gen_var g es te subnor_e_base subnor_m_base unpack_elen unpack_mlen in
    let inf_flag := returnInf in
    let zero_flag := returnZero in
    let nan_flag := returnNaN in
    let un_s := is_Btrue s in
    let un_e := Eite (returnInf \/# returnZero \/# returnNaN) defaultExponent
                (Eite returnNormal nor_e
                  subnor_e) in
    let un_m := Eite (returnInf \/# returnZero \/# returnNaN) defaultSignificand
                (Eite returnNormal nor_m
                  subnor_m) in
        make_unpackedbf_var gen_var g es te inf_flag zero_flag nan_flag un_s un_e un_m.
      
    Definition pack (bf : unpackedbf) : exp * exp * exp :=
      let s := un_s bf in
      let s_exp := Eite s (Econst [::true]) (Econst [::false]) in
      let e := un_e bf in
      let m := un_m bf in
      let returnInf := inf_flag bf in
      let returnZero := zero_flag bf in
      let returnNaN := nan_flag bf in
      let returnNormal := is_in_normal_range_bexp e unpack_elen in
      let unsigned_e := Ebinop Badd e bias_exp in
      let nor_packed_e := Eunop (Ulow elen) unsigned_e in
      let nor_packed_m := Eunop (Ulow mlen) m in
    (*   let pack_normal := nor_packed_m ++# nor_packed_e ++# s_exp in *)
      (* for subnormal number *)
     (*  let shift_amount := Ebinop Bsub (zero_exp unpack_elen) unsigned_e in *)
      let shift_amount := Ebinop Bsub min_normal_e_exp e in
      (* extend for wellform *)
      let shift_amount := if unpack_elen <= unpack_mlen then Eunop (Usext (unpack_mlen - unpack_elen)) shift_amount else Eunop (Ulow unpack_mlen) shift_amount in
      let shr_m := Ebinop Blshr m shift_amount in
      let subnor_packed_m := Eunop (Ulow mlen) shr_m in
      let zero_e := zero_exp elen in
    (*   let pack_subnormal := subnor_packed_m ++# zero_e ++# s_exp in *)
      let packed_s := Eite returnNaN Btrue_exp s_exp in
      let packed_e := Eite (returnNaN \/# returnInf) (ones_exp elen)
                      (Eite returnZero (zero_exp elen)
                      (Eite returnNormal nor_packed_e zero_e)) in
      let packed_m := Eite returnNaN (ones_exp mlen)
                      (Eite (returnInf \/# returnZero) (zero_exp mlen)
                      (Eite returnNormal nor_packed_m subnor_packed_m)) in
        (packed_s, packed_e, packed_m).

End Packing.
