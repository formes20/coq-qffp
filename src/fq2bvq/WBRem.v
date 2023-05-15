From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From ssrlib Require Import EqVar.
From Coq Require Import ZArith.
From nbits Require Import NBits.
From BitBlasting Require Import Typ TypEnv State.
From BitBlasting Require Import QFBV.
From WordBlasting Require Import WBCommon WBPacking WBRounding WBAddSub.

Import QFBV.
Import QFBVNotation.

Section Rem.

  Variable mlen elen: nat.
  
  Notation unpack_elen := (unpack_elen mlen elen).
  Notation unpack_mlen := (unpack_mlen mlen).
  Notation defaultExponent := (defaultExponent mlen elen).
  Notation defaultSignificand := (defaultSignificand mlen).
  Notation max_normal_e := (max_normal_e elen).
  Notation min_subnormal_e := (min_subnormal_e mlen elen).
  Notation round := (round mlen elen).
  Notation make_unpackedbf_var := ( make_unpackedbf_var mlen elen).
  
  Definition divide_step (remainder divider : exp) (bs_size : nat) : exp * bexp :=
    let can_subtract := remainder >=u?# divider in
    let subed_remainder := Ebinop Bsub remainder divider in
    let next_remainder := Eite can_subtract
                        (Ebinop Bshl subed_remainder (one_exp bs_size))
                        (Ebinop Bshl remainder (one_exp bs_size)) in
      (next_remainder, can_subtract).
  
  Fixpoint divide_loop (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (remainder divider : exp) (iter_exp : exp) (bs_size iter_size : nat) (loop_iter : nat) : SSATE.env * nat * seq bexp * exp :=
    match loop_iter with 
    | 0 => (te, g, es, remainder)
    | S loop_iter' => let next_remainder := (divide_step remainder divider bs_size).1 in
                      let needPrevious := iter_exp >=s?# (Econst (from_nat iter_size loop_iter)) in
                      let active_remainder := Eite needPrevious next_remainder remainder in
                      let '(te, g, es, active_remainder) := make_exp_var gen_var g es te active_remainder bs_size in
                        divide_loop gen_var g es te active_remainder divider iter_exp bs_size iter_size loop_iter'
    end.

  Definition remrne_unpackbf (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (bf1 bf2 : unpackedbf) : SSATE.env * nat * seq bexp * unpackedbf :=
    (* special case *)
    let eitherNaN := (nan_flag bf1) \/# (nan_flag bf2) in
    let returnNaN := eitherNaN \/# (inf_flag bf1) \/# (zero_flag bf2) in
    let rightInf := (~~# (inf_flag bf1)) /\# (inf_flag bf2) in
    let leftZero := (zero_flag bf1) /\# (~~# (nan_flag bf2)) in
    let returnLeft := rightInf \/# leftZero in
    (* normal and subnormal case *)
    let s1 := un_s bf1 in
    let e1 := un_e bf1 in
    let m1 := un_m bf1 in 
    let s2 := un_s bf2 in
    let e2 := un_e bf2 in
    let m2 := un_m bf2 in
    let result_sign := s1 in
    let ext_e1 := Eunop (Usext 1) e1 in
    let ext_e2 := Eunop (Usext 1) e2 in
    let e_diff := Ebinop Bsub ext_e1 ext_e2 in
    let ed_size := unpack_elen + 1 in
    let ext_m1 := Eunop (Uzext 1) m1 in
    let ext_m2 := Eunop (Uzext 1) m2 in
    let ext_m_size := unpack_mlen + 1 in
    let max_e_diff := Z.to_nat (max_normal_e - min_subnormal_e) in
    let '(te, g, es, r) := divide_loop gen_var g es te ext_m1 ext_m2 e_diff ext_m_size ed_size max_e_diff in
    let lsbRoundActive := e_diff >=s?# (zero_exp ed_size) in   (* e_diff >= 0 *)
    let needPrevious := e_diff >s?# (zero_exp ed_size)  in  (* e_diff > 0 *)
    let r0 := Eite needPrevious r ext_m1 in
    let (dsr_result, dsr_rembit) := divide_step r0 ext_m2 ext_m_size in
    let intergerEven := (~~# lsbRoundActive) \/# (~~# dsr_rembit) in
    let guardRoundActive := e_diff >=s?# (Econst (from_Z ed_size (-1)%Z)) in  (* e_diff >= -1 *)
    let rm1 := Eite lsbRoundActive dsr_result ext_m1 in
    let (dsrg_result, dsrg_rembit) := divide_step rm1 ext_m2 ext_m_size in
    let guard_bit := guardRoundActive /\# dsrg_rembit in
    let sticky_bit := ~~# (is_all_zeros (Eite guardRoundActive dsrg_result ext_m1) ext_m_size) in
    let e := e2 in
    let m := Eunop (Uhigh unpack_mlen) dsr_result in
    let returnZero := is_all_zeros m unpack_mlen in
    let '(te, g, es, normal_e, normal_m) := normalize gen_var g es te e m unpack_elen unpack_mlen in
    let candidate_e := Eite lsbRoundActive (Eite returnZero defaultExponent normal_e) e1 in
    let candidate_m := Eite lsbRoundActive (Eite returnZero defaultSignificand normal_m) m1 in
    let '(te, g, es, candidate_e) := make_exp_var gen_var g es te candidate_e unpack_elen in
    let '(te, g, es, candidate_m) := make_exp_var gen_var g es te candidate_m unpack_mlen in
    let candidate_result := Build_unpackedbf Bfalse returnZero Bfalse result_sign candidate_e candidate_m in
    (* rne rounding *)
    let bonusSubtract := guard_bit /\# (sticky_bit \/# (~~# intergerEven)) in
    let '(te, g, es, subed_result) := (add_unpackbf' mlen elen gen_var g es te rne_exp candidate_result bf2 (Bxor_bexp s1 s2)) in
    let inf_flag := Eite_bexp returnNaN Bfalse
              (Eite_bexp returnLeft (inf_flag bf1)
              (Eite_bexp bonusSubtract (inf_flag subed_result)
                (inf_flag candidate_result))) in
    let zero_flag := Eite_bexp returnNaN Bfalse
                    (Eite_bexp returnLeft (zero_flag bf1)
                    (Eite_bexp bonusSubtract (zero_flag subed_result)
                      (zero_flag candidate_result))) in
    let nan_flag := Eite_bexp returnNaN Btrue Bfalse in
    let un_s := Eite_bexp returnNaN Btrue 
                  (Eite_bexp returnLeft s1
                  (Eite_bexp bonusSubtract (un_s subed_result)
                    (un_s candidate_result))) in
    let un_e := Eite returnNaN defaultExponent
                (Eite returnLeft e1
                (Eite bonusSubtract (un_e subed_result)
                  (un_e candidate_result))) in
    let un_m := Eite returnNaN defaultSignificand
                (Eite returnLeft m1
                (Eite bonusSubtract (un_m subed_result)
                  (un_m candidate_result))) in
      make_unpackedbf_var gen_var g es te inf_flag zero_flag nan_flag un_s un_e un_m.

  Notation unpack := (unpack mlen elen).
  Notation pack := (pack mlen elen).
  
  Definition rem (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (s1 e1 m1 s2 e2 m2 : exp) : SSATE.env * nat * seq bexp * (exp * exp * exp) :=
    let '(te, g, es, ubf1) := unpack gen_var g es te s1 e1 m1 in
    let '(te, g, es, ubf2) := unpack gen_var g es te s2 e2 m2 in
    let '(te, g, es, unpack_result) := remrne_unpackbf gen_var g es te ubf1 ubf2 in
    let repack_result := pack unpack_result in
      (te, g, es, repack_result).
      
End Rem.
