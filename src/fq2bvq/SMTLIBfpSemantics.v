From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From Coq Require Import Reals Reals.ROrderedType.
From nbits Require Import NBits.

From mathcomp Require Import seq eqtype ssrfun ssrbool ssrnat ssreflect.

From BitBlasting Require Import Typ TypEnv State AdhereConform QFBV.
From WordBlasting Require Import fq2bvq.

Declare Scope ER_scope.
Delimit Scope ER_scope with ER.

Section AddtionalBop.
    Definition is_ones (bs : bits) : bool := all (fun b => b == true) bs.
    
    Lemma size_ones n : size (ones n) = n.
    Proof. exact: size_nseq. Qed.
    
    Lemma is_ones_ones bs : is_ones bs -> bs = ones (size bs).
    Proof.
      elim: bs => [| b bs IH] //=. move/andP=> [H1 H2]. rewrite (eqP H1).
      rewrite (IH H2). rewrite size_ones. reflexivity.
    Qed.
  
    Lemma ones_is_ones n : is_ones (ones n).
      Proof. by elim: n. Qed.
  
    Lemma is_ones_equiv_ones bs : is_ones bs <-> bs = ones (size bs).
    Proof.
      split; first exact: is_ones_ones. move=> ->; exact: ones_is_ones.
    Qed.

    Lemma is_ones_eq_ones bs : is_ones bs = (bs == ones (size bs)).
    Proof.
      case H0 : (is_ones bs); case H0s : (bs == ones (size bs)); try done.
      - move/eqP in H0. rewrite eqb_id in H0. apply is_ones_equiv_ones in H0. 
        rewrite {1}H0 eqxx in H0s. assumption. 
      - move/eqP in H0s. apply is_ones_equiv_ones in H0s. rewrite H0s in H0.
        by rewrite H0.
    Qed.
    
    Lemma ones_cons n : b1::ones n = ones n.+1.
    Proof. reflexivity. Qed.
    
    Lemma ones_rcons n : rcons (ones n) b1 = ones n.+1.
    Proof. elim: n => [| n IHn] //=. rewrite ones_cons IHn. reflexivity. Qed.
      

End AddtionalBop.

Section ExtReal.

  Variant ExtendReal :=
    | RN (r : R)
    | RI (s : bool)
    | RNaN.
  
  Open Scope R_scope.

  Inductive EReq_rel : ExtendReal -> ExtendReal -> Prop :=
  | isRNRNeq : forall r1 r2, r1 = r2 -> EReq_rel (RN r1) (RN r2)
  | isRIRIeq : forall s1 s2, s1 = s2 -> EReq_rel (RI s1) (RI s2).
    
  Inductive ERlt_rel : ExtendReal -> ExtendReal -> Prop :=
  | isRNRNlt : forall r1 r2, Rlt r1 r2 -> ERlt_rel (RN r1) (RN r2)
  | isRIRNlt : forall s r, s = true -> ERlt_rel (RI s) (RN r)
  | isRNRIlt : forall r s, s = false -> ERlt_rel (RN r) (RI s)
  | isRIRIlt : forall s1 s2, (s1 = true /\ s2 = false) -> ERlt_rel (RI s1) (RI s2).

  Definition ERle_rel (er1 er2 : ExtendReal) := (EReq_rel er1 er2) \/ (ERlt_rel er1 er2).
  Definition ERgt_rel (er1 er2 : ExtendReal) := ERlt_rel er2 er1.
  Definition ERge_rel (er1 er2 : ExtendReal) := ERle_rel er2 er1.

  Inductive ERopp_rel : ExtendReal -> ExtendReal -> Prop :=
    | OppRNaN : ERopp_rel RNaN RNaN
    | OppRI : forall s, ERopp_rel (RI s) (RI (~~s))
    | OppRN : forall r, ERopp_rel (RN r) (RN (-r)).

  Inductive ERplus_rel : ExtendReal -> ExtendReal -> ExtendReal -> Prop :=
    | PlusLeftNaN : forall er, ERplus_rel RNaN er RNaN
    | PlusRightNaN : forall er, ERplus_rel er RNaN RNaN
    | PlusXnorRI : forall s, ERplus_rel (RI s) (RI s) (RI s)
    | PlusXorRI : forall s, ERplus_rel (RI s) (RI (~~s)) RNaN
    | PlusRIRN : forall s r, ERplus_rel (RI s) (RN r) (RI s)
    | PlusRNRI : forall s r, ERplus_rel (RN r) (RI s) (RI s)
    | PlusRNRN : forall r1 r2, ERplus_rel (RN r1) (RN r2) (RN (r1 + r2)).
  
  Inductive ERsub_rel : ExtendReal -> ExtendReal -> ExtendReal -> Prop :=
    | SubLeftNaN : forall er, ERsub_rel RNaN er RNaN
    | SubRightNaN : forall er, ERsub_rel er RNaN RNaN
    | SubXnorRI : forall s, ERsub_rel (RI s) (RI s) RNaN
    | SubXorRI : forall s, ERsub_rel (RI s) (RI (~~s)) (RI s)
    | SubRIRN : forall s r, ERsub_rel (RI s) (RN r) (RI s)
    | SubRNRI : forall s r, ERsub_rel (RN r) (RI s) (RI s)
    | SubRNRN : forall r1 r2, ERsub_rel (RN r1) (RN r2) (RN (r1 - r2)).
    
  Inductive ERmul_rel : ExtendReal -> ExtendReal -> ExtendReal -> Prop :=
    | MulLeftNaN : forall er, ERmul_rel RNaN er RNaN
    | MulRightNaN : forall er, ERmul_rel er RNaN RNaN
    | MulXnorRI : forall s, ERmul_rel (RI s) (RI s) (RI false)
    | MulXorRI : forall s, ERmul_rel (RI s) (RI (~~s)) (RI true)
    | MulRIRN0 : forall s, ERmul_rel (RI s) (RN 0) RNaN
    | MulRIPRN : forall s r, r > 0 -> ERmul_rel (RI s) (RN r) (RI s)
    | MulRINRN : forall s r, r < 0 -> ERmul_rel (RI s) (RN r) (RI (~~s))
    | MulRN0RI : forall s, ERmul_rel (RN 0) (RI s) RNaN
    | MulPRNRI : forall r s, r > 0 -> ERmul_rel (RN r) (RI s) (RI s)
    | MulNRNRI : forall r s, r < 0 -> ERmul_rel (RN r) (RI s) (RI (~~s))
    | MulRNRN : forall r1 r2, ERmul_rel (RN r1) (RN r2) (RN (r1 * r2)).
  
  Inductive ERinv_rel : ExtendReal -> ExtendReal -> Prop :=
    | invRNaN : ERinv_rel RNaN RNaN
    | invRI : forall s, ERinv_rel (RI s) (RN 0)
    | invRN0 : ERinv_rel (RN 0) (RI false)
    | invRN : forall r, ERinv_rel (RN r) (RN (/r)).
 
  Inductive ERdiv_rel : ExtendReal -> ExtendReal -> ExtendReal -> Prop :=
    | divByMulInv : forall er2 inv_er, ERinv_rel er2 inv_er -> 
                    forall er1 mul_er, ERmul_rel er1 inv_er mul_er ->
                      ERdiv_rel er1 er2 mul_er.

  Definition ERpow (er : ExtendReal) (n : nat) : ExtendReal :=
    match er with
    | RNaN => RNaN
    | RI false => RI false
    | RI true => if (n mod 2 == 0)%nat then RI false else RI true
    | RN r => RN (pow r n)
    end.
    
  Inductive ERpow_rel : ExtendReal -> nat -> ExtendReal -> Prop :=
  | PowRNaN : forall n, ERpow_rel RNaN n RNaN
  | PowPRI : forall n, ERpow_rel (RI false) n (RI false)
  | PowNRIeven : forall n, (n mod 2 == 0)%nat -> ERpow_rel (RI true) n (RI false)
  | PowNRIodd : forall n, (n mod 2 == 1)%nat -> ERpow_rel (RI true) n (RI true)
  | PowRN : forall r n, ERpow_rel (RN r) n (RN (pow r n)).
 
  Inductive ERsqrt_rel : ExtendReal -> ExtendReal -> Prop :=
    | SqrtRNaN : ERsqrt_rel RNaN RNaN
    | SqrtRI : forall s, ERsqrt_rel (RI s) RNaN
    | SqrtPRN : forall r, r >= 0 -> ERsqrt_rel (RN r) (RN (sqrt r))
    | SqrtNRN : forall r, r < 0 -> ERsqrt_rel (RN r) RNaN.
 
  Close Scope R_scope.
  
End ExtReal.
 
Module SMTLIBfp.

  Section Maps.
  
    Variable mlen elen : nat.  

    Inductive fp_format : Set :=
    | ieee754_fp (s : bits) (e : bits) (m : bits).
    
    Definition build_bits (bf : fp_format) : bits :=
      match bf with
      | ieee754_fp s e m => m ++ e ++ s
      end.
    
    Definition from_bits (bs : bits) : fp_format :=
      let s := high 1 bs in
      let e := extract (elen - 1 + mlen) mlen bs in
      let m := extract (mlen - 1) 0 bs in
        ieee754_fp s e m.
    
    Inductive well_formed_ieee754_rel : nat -> nat -> fp_format -> Prop :=
    | isValSize : forall mlen elen s e m, 1 < mlen -> 1 < elen -> elen <= mlen ->
                    size s = 1 -> size e = elen -> size m = mlen ->
                    well_formed_ieee754_rel mlen elen (ieee754_fp s e m).
    
    Definition sign_bv (bf : fp_format) := 
      match bf with
      | ieee754_fp s _ _ => s
      end.
    
    (* Default value is 1...1 *)
    Definition NaN := ieee754_fp [::true] (ones elen) (ones mlen).
    Definition pos_infinity := ieee754_fp [::false] (ones elen) (zeros mlen).
    Definition neg_infinity := ieee754_fp [::true] (ones elen) (zeros mlen).
    Definition pos_zero := ieee754_fp [::false] (zeros elen) (zeros mlen).
    Definition neg_zero := ieee754_fp [::true] (zeros elen) (zeros mlen).
    Definition one := ieee754_fp [::false] (ones (elen-1)) (zeros mlen).
    
    Definition sign (bf : fp_format) := msb (sign_bv bf).
    
    Definition bexp (bf : fp_format) := 
      match bf with
      | ieee754_fp _ e _ => e
      end.
      
    Definition bmantissa (bf : fp_format) := 
      match bf with
      | ieee754_fp _ _ m => m
      end.

    Definition bias := 2^(elen-1)-1.
  
    Definition sign_to_ER (s : bool) : ExtendReal := if s then RN (-1)%R else RN 1%R.

    Inductive FS_exp_rel : ExtendReal -> Prop :=
      | FS_exp : forall er, ERpow_rel (RN (/2)) (bias-1) er -> FS_exp_rel er.
    
   (*  Definition N_exponent_to_ER (e : bits) := ERpow_distance (RN 2) (to_nat e) (bias (size e)) . *)
    
    Inductive ERpow_x_minus_y_rel : ExtendReal -> nat -> nat -> ExtendReal -> Prop :=
      | PowXGeY : forall x y, x >= y -> 
                  forall er pow_er, ERpow_rel er (x-y) pow_er -> 
                    ERpow_x_minus_y_rel er x y pow_er
      | PowXltY : forall x y, x < y -> 
                  forall er inv_er, ERinv_rel er inv_er -> 
                  forall pow_er, ERpow_rel inv_er (y-x) pow_er -> 
                    ERpow_x_minus_y_rel er x y pow_er. 
    
    Inductive FN_exp_rel : bits -> ExtendReal -> Prop :=
      | FN_exp : forall e er, ERpow_x_minus_y_rel (RN 2) (to_nat e) bias er ->
                   FN_exp_rel e er.
                   
    Inductive mantissa_rel : bits -> ExtendReal -> Prop :=
      | mantissa : forall denominator, ERpow_rel (RN 2) mlen denominator ->
                   forall m er, ERdiv_rel (RN (IZR (Z.of_nat (to_nat m)))) denominator er ->
                     mantissa_rel m er.
      
    Inductive v_rel : fp_format -> ExtendReal -> Prop :=
      | ofFNaN : forall fp, well_formed_ieee754_rel mlen elen fp ->
                    forall s e m, fp = (ieee754_fp s e m) ->
                      (is_ones e) && ~~(is_zero m) ->
                        v_rel fp RNaN
      | ofFZ : forall fp, well_formed_ieee754_rel mlen elen fp ->
                    forall s e m, fp = (ieee754_fp s e m) ->
                      (is_zero e) && (is_zero m) ->
                        v_rel fp (RN 0)
      | ofFI : forall fp, well_formed_ieee754_rel mlen elen fp ->
                    forall s e m, fp = (ieee754_fp s e m) ->
                      (is_ones e) && (is_zero m) ->
                        v_rel fp (RI (msb s))
      | ofFS : forall fp, well_formed_ieee754_rel mlen elen fp ->
                    forall s e m, fp = (ieee754_fp s e m) ->
                      (is_zero e) && ~~(is_zero m) ->
                        forall exp, FS_exp_rel exp ->
                        forall man, mantissa_rel m man ->
                        forall product1, ERmul_rel (sign_to_ER (msb s)) exp product1 ->
                        forall product2, ERmul_rel product1 man product2 ->
                          v_rel fp product2
      | ofFN : forall fp, well_formed_ieee754_rel mlen elen fp ->
                    forall s e m, fp = (ieee754_fp s e m) ->
                      ~~(is_ones e) && ~~(is_zero e) ->
                        forall exp, FN_exp_rel e exp ->
                        forall man, mantissa_rel m man ->
                        forall product1, ERmul_rel (sign_to_ER (msb s)) exp product1 ->
                        forall product2, ERmul_rel product1 man product2 ->
                        forall sum, ERplus_rel (RN 1) product2 sum ->
                          v_rel fp sum.

    Inductive total_order_fp_rel : fp_format -> fp_format -> Prop :=
      | NegPos : forall s1 e1 m1 s2 e2 m2, 
                    well_formed_ieee754_rel mlen elen (ieee754_fp s1 e1 m1) ->
                    well_formed_ieee754_rel mlen elen (ieee754_fp s2 e2 m2) ->
                    ((msb s1) = true) /\ ((msb s2) = false) ->
                    total_order_fp_rel (ieee754_fp s1 e1 m1) (ieee754_fp s2 e2 m2)
      | PosPosExpLt : forall s1 e1 m1 s2 e2 m2, 
                        well_formed_ieee754_rel mlen elen (ieee754_fp s1 e1 m1) ->
                        well_formed_ieee754_rel mlen elen (ieee754_fp s2 e2 m2) ->
                        ((msb s1) = false) /\ ((msb s2) = false) ->
                        (to_nat e1) < (to_nat e2) ->
                        total_order_fp_rel (ieee754_fp s1 e1 m1) (ieee754_fp s2 e2 m2)
      | PosPosExpEq : forall s1 e1 m1 s2 e2 m2, 
                        well_formed_ieee754_rel mlen elen (ieee754_fp s1 e1 m1) ->
                        well_formed_ieee754_rel mlen elen (ieee754_fp s2 e2 m2) ->
                        ((msb s1) = false) /\ ((msb s2) = false) ->
                        (to_nat e1) = (to_nat e2) ->
                        (to_nat m1) <= (to_nat m2) ->
                        total_order_fp_rel (ieee754_fp s1 e1 m1) (ieee754_fp s2 e2 m2)
      | NegNegExpGt : forall s1 e1 m1 s2 e2 m2, 
                        well_formed_ieee754_rel mlen elen (ieee754_fp s1 e1 m1) ->
                        well_formed_ieee754_rel mlen elen (ieee754_fp s2 e2 m2) ->
                        ((msb s1) = true) /\ ((msb s2) = true) ->
                        (to_nat e1) > (to_nat e2) ->
                        total_order_fp_rel (ieee754_fp s1 e1 m1) (ieee754_fp s2 e2 m2)
      | NegNegExpEq : forall s1 e1 m1 s2 e2 m2, ((msb s1) = true) /\ ((msb s2) = true) ->
                        well_formed_ieee754_rel mlen elen (ieee754_fp s1 e1 m1) ->
                        well_formed_ieee754_rel mlen elen (ieee754_fp s2 e2 m2) ->
                        (to_nat e1) = (to_nat e2) ->
                        (to_nat m1) >= (to_nat m2) ->
                        total_order_fp_rel (ieee754_fp s1 e1 m1) (ieee754_fp s2 e2 m2).
                        
    Inductive partial_order_fp_rel : fp_format -> fp_format -> Prop :=
      | NaNNaN : forall s1 e1 m1 s2 e2 m2, 
                   well_formed_ieee754_rel mlen elen (ieee754_fp s1 e1 m1) ->
                   well_formed_ieee754_rel mlen elen (ieee754_fp s2 e2 m2) ->
                   (is_ones e1) && ~~(is_zero m1) && (is_ones e2) && ~~(is_zero m2) ->
                   partial_order_fp_rel (ieee754_fp s1 e1 m1) (ieee754_fp s2 e2 m2)
      | NeitherNaN : forall s1 e1 m1 s2 e2 m2, 
                       well_formed_ieee754_rel mlen elen (ieee754_fp s1 e1 m1) ->
                       well_formed_ieee754_rel mlen elen (ieee754_fp s2 e2 m2) ->
                       ~( ((is_ones e1) && ~~(is_zero m1)) || 
                          ((is_ones e2) && ~~(is_zero m2)) ) ->
                       total_order_fp_rel (ieee754_fp s1 e1 m1) (ieee754_fp s2 e2 m2) ->
                       partial_order_fp_rel (ieee754_fp s1 e1 m1) (ieee754_fp s2 e2 m2).
      
    (* vtr and vbr would be wellformed because of the precondition of total_order_fp_rel, 
       so the result of rnd would be wellformed *)
    Inductive v_top_rel : ExtendReal -> fp_format -> Prop :=
      | v_top : forall r x vx, (v_rel x vx) /\ (ERle_rel r vx) ->
                   forall vtr, partial_order_fp_rel vtr x ->
                   forall v_vtr, (v_rel vtr v_vtr) /\ (ERle_rel r v_vtr) ->
                     v_top_rel r vtr.
    
    Inductive v_bottom_rel : ExtendReal -> fp_format -> Prop :=
      | v_bottom : forall r x vx, (v_rel x vx) /\ (ERle_rel vx r) ->
                   forall vbr, partial_order_fp_rel x vbr ->
                   forall v_vbr, (v_rel vbr v_vbr) /\ (ERle_rel v_vbr r) ->
                     v_bottom_rel r vbr.
      
    Inductive v_int_rel : Z -> ExtendReal -> Prop :=
      | v_int : forall z, v_int_rel z (RN (IZR z)).
      
    Inductive total_order_int_rel : Z -> Z -> Prop :=
      | total_order_int : forall z1 z2, (z1 < z2)%Z -> total_order_int_rel z1 z2.
      
    Inductive v_int_top_rel : ExtendReal -> Z -> Prop :=
      | v_int_top : forall r x vx, (v_int_rel x vx) /\ (ERle_rel r vx) ->
                    forall vtr, total_order_int_rel vtr x ->
                    forall v_vtr, (v_int_rel vtr v_vtr) /\ (ERle_rel r v_vtr) ->
                      v_int_top_rel r vtr.

    Inductive v_int_bottom_rel : ExtendReal -> Z -> Prop :=
      | v_intbottom : forall r x vx, (v_int_rel x vx) /\ (ERle_rel vx r) ->
                      forall vbr, total_order_int_rel x vbr ->
                      forall v_vbr, (v_int_rel vbr v_vbr) /\ (ERle_rel v_vbr r) ->
                        v_int_bottom_rel r vbr.

  End Maps.
  
  Section Rounding.
  
    Variable mlen elen : nat.  
      
    Inductive ev_rel : fp_format -> Prop :=
      | evNotNaN : forall s e m, ~~((is_ones e) && (~~ is_zero m)) ->
                    Z.even (to_Z m) -> ev_rel (ieee754_fp s e m).

    Inductive lh_rel : ExtendReal -> Prop :=
      | lh : forall r vbr, v_bottom_rel mlen elen r vbr ->
             forall vbr', v_bottom_rel (mlen+1) elen r vbr' ->
             forall v_vbr v_vbr', (v_rel mlen elen vbr v_vbr) /\ 
                                  (v_rel (mlen+1) elen vbr' v_vbr') /\ 
                                  (EReq_rel v_vbr v_vbr') -> 
               lh_rel r.

    Inductive tb_rel : ExtendReal -> Prop :=
      | tb :  forall r vbr, v_bottom_rel mlen elen r vbr ->
              forall vbr', v_bottom_rel (mlen+1) elen r vbr' ->
              forall v_vbr v_vbr', (v_rel mlen elen vbr v_vbr) /\ 
                                   (v_rel (mlen+1) elen vbr' v_vbr') /\ 
                                   (ERlt_rel v_vbr v_vbr') -> 
              forall vtr, v_top_rel mlen elen r vtr ->
              forall vtr', v_top_rel (mlen+1) elen r vtr' ->
              forall v_vtr v_vtr', (v_rel mlen elen vtr v_vtr) /\ 
                                   (v_rel (mlen+1) elen vtr' v_vtr') /\ 
                                   (ERlt_rel v_vtr' v_vtr) ->
                tb_rel r.
     
    (* direct definition *)
    Inductive ev_int_rel : Z -> Prop := 
      | evInt : forall z, Z.even z -> ev_int_rel z.
      
    Inductive lh_int_rel : ExtendReal -> Prop :=
      | lhInt : forall r vtr vbr, (v_int_top_rel r vtr) /\ (v_int_bottom_rel r vbr) ->
                forall v_vtr v_vbr, (v_int_rel vtr v_vtr) /\ (v_int_rel vbr v_vbr) ->
                forall leftdiff, ERsub_rel r v_vbr leftdiff ->
                forall rightdiff, ERsub_rel v_vtr r rightdiff ->
                  ERlt_rel leftdiff rightdiff -> lh_int_rel r. 

    Inductive tb_int_rel : ExtendReal -> Prop :=
      | tbInt : forall r vtr vbr, (v_int_top_rel r vtr) /\ (v_int_bottom_rel r vbr) ->
                forall v_vtr v_vbr, (v_int_rel vtr v_vtr) /\ (v_int_rel vbr v_vbr) ->
                forall leftdiff, ERsub_rel r v_vbr leftdiff ->
                forall rightdiff, ERsub_rel v_vtr r rightdiff ->
                  EReq_rel leftdiff rightdiff -> tb_int_rel r. 
    
    Definition rsz (zs : bool) := 
      if zs then v_top_rel else v_bottom_rel.
      
    Inductive round_nearest_even_rel : bool -> ExtendReal 
                                       -> (nat -> nat -> ExtendReal -> fp_format -> Prop) -> Prop:=
    | rneNaN : forall zs, round_nearest_even_rel zs RNaN v_bottom_rel
    | rneZero : forall zs, round_nearest_even_rel zs (RN 0) (rsz zs)
    | rneHighHalf : forall zs r, ~(EReq_rel r (RN 0)) /\ ~(lh_rel r) /\ ~(tb_rel r) ->
                      round_nearest_even_rel zs r v_top_rel
    | rneMidHighEven : forall zs r, ~(EReq_rel r (RN 0)) /\ (tb_rel r) ->
                       forall vtr, (v_top_rel mlen elen r vtr) /\ (ev_rel vtr) ->
                        round_nearest_even_rel zs r v_top_rel
    | rneMidLowEven : forall zs r, ~(EReq_rel r (RN 0)) /\ (tb_rel r) ->
                       forall vbr, (v_bottom_rel mlen elen r vbr) /\ (ev_rel vbr) ->
                        round_nearest_even_rel zs r v_bottom_rel
    | rneLowHalf : forall zs r, ~(EReq_rel r (RN 0)) /\ (lh_rel r) ->
                      round_nearest_even_rel zs r v_bottom_rel.

    Inductive round_nearest_away_zero_rel : bool -> ExtendReal 
                                            -> (nat -> nat -> ExtendReal -> fp_format -> Prop) -> Prop:=
    | rnaNaN : forall zs, round_nearest_away_zero_rel zs RNaN v_bottom_rel
    | rnaZero : forall zs, round_nearest_away_zero_rel zs (RN 0) (rsz zs)
    | rnaPosHighHalf : forall zs r, (ERgt_rel r (RN 0)) /\ ~(lh_rel r) -> 
                         round_nearest_away_zero_rel zs r v_top_rel
    | rnaPosLowHalf : forall zs r, (ERgt_rel r (RN 0)) /\ (lh_rel r) -> 
                         round_nearest_away_zero_rel zs r v_bottom_rel
    | rnaNegHighHalf : forall zs r, (ERlt_rel r (RN 0)) /\ ~(lh_rel r) /\ ~(tb_rel r) -> 
                         round_nearest_away_zero_rel zs r v_top_rel
    | rnaNegLowHalf : forall zs r, (ERlt_rel r (RN 0)) /\ ((lh_rel r) \/ (tb_rel r)) -> 
                         round_nearest_away_zero_rel zs r v_bottom_rel.
                         
    Inductive round_towards_posinfinity_rel : bool -> ExtendReal 
                                          -> (nat -> nat -> ExtendReal -> fp_format -> Prop) -> Prop:=
    | rtpZero : forall zs, round_towards_posinfinity_rel zs (RN 0) (rsz zs)
    | rtpOtherwise : forall zs r, ~(EReq_rel r (RN 0)) -> round_towards_posinfinity_rel zs r v_top_rel.

    Inductive round_towards_neginfinity_rel : bool -> ExtendReal 
                                          -> (nat -> nat -> ExtendReal -> fp_format -> Prop) -> Prop:=
    | rtnZero : forall zs, round_towards_neginfinity_rel zs (RN 0) (rsz zs)
    | rtnOtherwise : forall zs r, ~(EReq_rel r (RN 0)) -> round_towards_neginfinity_rel zs r v_bottom_rel.
    
    Inductive round_towards_zero_rel : bool -> ExtendReal 
                                          -> (nat -> nat -> ExtendReal -> fp_format -> Prop) -> Prop:=
    | rtzZero : forall zs, round_towards_zero_rel zs (RN 0) (rsz zs)
    | rtzPos : forall zs r, (ERgt_rel r (RN 0)) -> round_towards_zero_rel zs r v_bottom_rel
    | rtzNeg : forall zs r, (ERlt_rel r (RN 0)) -> round_towards_zero_rel zs r v_top_rel.

    Variant RoundingMode := 
    | rne
    | rna
    | rtp
    | rtn
    | rtz.

    Inductive bits_RM_rel : bits -> RoundingMode -> Prop :=
      | rneBits : bits_RM_rel [::false;false;false] rne
      | rnaBits : bits_RM_rel [::true;false;false] rna
      | rtpBits : bits_RM_rel [::false;true;false] rtp
      | rtnBits : bits_RM_rel [::true;true;false] rtn
      | rtzBits : bits_RM_rel [::false;false;true] rtz.
      
    Inductive rnd_rel : RoundingMode -> bool -> ExtendReal -> fp_format -> Prop :=
      | RNERounding : forall zs er rnd, round_nearest_even_rel zs er rnd ->
                      forall rnd_fp, rnd mlen elen er rnd_fp -> rnd_rel rne zs er rnd_fp
      | RNARounding : forall zs er rnd, round_nearest_away_zero_rel zs er rnd ->
                      forall rnd_fp, rnd mlen elen er rnd_fp -> rnd_rel rna zs er rnd_fp
      | RTPRounding : forall zs er rnd, round_towards_posinfinity_rel zs er rnd ->
                      forall rnd_fp, rnd mlen elen er rnd_fp -> rnd_rel rtp zs er rnd_fp
      | RTNRounding : forall zs er rnd, round_towards_neginfinity_rel zs er rnd ->
                      forall rnd_fp, rnd mlen elen er rnd_fp -> rnd_rel rtn zs er rnd_fp
      | RTZRounding : forall zs er rnd, round_towards_zero_rel zs er rnd ->
                      forall rnd_fp, rnd mlen elen er rnd_fp -> rnd_rel rtz zs er rnd_fp.

    Definition rsz_int (zs : bool) := 
      if zs then v_int_top_rel else v_int_bottom_rel.
      
    Inductive round_nearest_even_int_rel : bool -> ExtendReal 
                                       -> (ExtendReal -> Z -> Prop) -> Prop:=
    | rneIntNaN : forall zs, round_nearest_even_int_rel zs RNaN v_int_bottom_rel
    | rneIntZero : forall zs, round_nearest_even_int_rel zs (RN 0) (rsz_int zs)
    | rneIntHighHalf : forall zs r, ~(EReq_rel r (RN 0)) /\ ~(lh_int_rel r) /\ ~(tb_int_rel r) ->
                      round_nearest_even_int_rel zs r v_int_top_rel
    | rneIntMidHighEven : forall zs r, ~(EReq_rel r (RN 0)) /\ (tb_int_rel r) ->
                       forall vtr, (v_int_top_rel r vtr) /\ (ev_int_rel vtr) ->
                        round_nearest_even_int_rel zs r v_int_top_rel
    | rneIntMidLowEven : forall zs r, ~(EReq_rel r (RN 0)) /\ (tb_int_rel r) ->
                       forall vbr, (v_int_bottom_rel r vbr) /\ (ev_int_rel vbr) ->
                        round_nearest_even_int_rel zs r v_int_bottom_rel
    | rneIntLowHalf : forall zs r, ~(EReq_rel r (RN 0)) /\ (lh_int_rel r) ->
                      round_nearest_even_int_rel zs r v_int_bottom_rel.

    Inductive round_nearest_away_zero_int_rel : bool -> ExtendReal 
                                       -> (ExtendReal -> Z -> Prop) -> Prop:=
    | rnaIntNaN : forall zs, round_nearest_away_zero_int_rel zs RNaN v_int_bottom_rel
    | rnaIntZero : forall zs, round_nearest_away_zero_int_rel zs (RN 0) (rsz_int zs)
    | rnaIntPosHighHalf : forall zs r, (ERgt_rel r (RN 0)) /\ ~(lh_int_rel r) -> 
                      round_nearest_away_zero_int_rel zs r v_int_top_rel
    | rnaIntPosLowHalf : forall zs r, (ERgt_rel r (RN 0)) /\ (lh_int_rel r) -> 
                      round_nearest_away_zero_int_rel zs r v_int_bottom_rel
    | rnaIntNegHighHalf: forall zs r, (ERlt_rel r (RN 0)) /\ ~(lh_int_rel r) /\ ~(tb_int_rel r) -> 
                        round_nearest_away_zero_int_rel zs r v_int_top_rel
    | rnaIntNegLowHalf : forall zs r, (ERlt_rel r (RN 0)) /\ ((lh_int_rel r) \/ (tb_int_rel r)) -> 
                      round_nearest_away_zero_int_rel zs r v_int_bottom_rel.

    Inductive round_towards_posinfinity_int_rel : bool -> ExtendReal 
                                          -> (ExtendReal -> Z -> Prop) -> Prop:=
    | rtpIntZero : forall zs, round_towards_posinfinity_int_rel zs (RN 0) (rsz_int zs)
    | rtpIntOtherwise : forall zs r, ~(EReq_rel r (RN 0)) -> 
                          round_towards_posinfinity_int_rel zs r v_int_top_rel.

    Inductive round_towards_neginfinity_int_rel : bool -> ExtendReal 
                                          -> (ExtendReal -> Z -> Prop) -> Prop:=
    | rtnIntZero : forall zs, round_towards_neginfinity_int_rel zs (RN 0) (rsz_int zs)
    | rtnIntOtherwise : forall zs r, ~(EReq_rel r (RN 0)) -> 
                          round_towards_neginfinity_int_rel zs r v_int_bottom_rel.
    
    Inductive round_towards_zero_int_rel : bool -> ExtendReal 
                                          -> (ExtendReal -> Z -> Prop) -> Prop:=
    | rtzIntZero : forall zs, round_towards_zero_int_rel zs (RN 0) (rsz_int zs)
    | rtzIntPos : forall zs r, (ERgt_rel r (RN 0)) -> round_towards_zero_int_rel zs r v_int_bottom_rel
    | rtzIntNeg : forall zs r, (ERlt_rel r (RN 0)) -> round_towards_zero_int_rel zs r v_int_top_rel.
    
    Inductive rnd_int_rel : RoundingMode -> bool -> ExtendReal -> Z -> Prop :=
      | IntRNERounding : forall zs er rnd, round_nearest_even_int_rel zs er rnd ->
                         forall rnd_int, rnd er rnd_int -> rnd_int_rel rne zs er rnd_int
      | IntRNARounding : forall zs er rnd, round_nearest_away_zero_int_rel zs er rnd ->
                         forall rnd_int, rnd er rnd_int -> rnd_int_rel rna zs er rnd_int
      | IntRTPRounding : forall zs er rnd, round_towards_posinfinity_int_rel zs er rnd ->
                      forall rnd_int, rnd er rnd_int -> rnd_int_rel rtp zs er rnd_int
      | IntRTNRounding : forall zs er rnd, round_towards_neginfinity_int_rel zs er rnd ->
                      forall rnd_int, rnd er rnd_int -> rnd_int_rel rtn zs er rnd_int
      | IntRTZRounding : forall zs er rnd, round_towards_zero_int_rel zs er rnd ->
                      forall rnd_int, rnd er rnd_int -> rnd_int_rel rtz zs er rnd_int.
                      
  End Rounding.

  Section Operations.
    Variable mlen elen : nat.  
      
    Inductive isNormal_rel : fp_format -> bool -> Prop :=
      | isNormal : forall s e m b, b = ~~(is_ones e) && ~~(is_zero e) -> 
                   well_formed_ieee754_rel mlen elen (ieee754_fp s e m) ->
                   isNormal_rel (ieee754_fp s e m) b.
      
    Inductive isSubNormal_rel : fp_format -> bool -> Prop :=
      | isSubNormal : forall s e m b, b = (is_zero e) && ~~(is_zero m) -> 
                      well_formed_ieee754_rel mlen elen (ieee754_fp s e m) ->
                      isSubNormal_rel (ieee754_fp s e m) b.

    Inductive isInfinite_rel : fp_format -> bool -> Prop :=
      | isInfinite : forall s e m b, b = (is_ones e) && (is_zero m) -> 
                     well_formed_ieee754_rel mlen elen (ieee754_fp s e m) ->
                     isInfinite_rel (ieee754_fp s e m) b.
      
    Inductive isNaN_rel : fp_format -> bool -> Prop :=
      | isNaN : forall s e m b, b = (is_ones e) && ~~(is_zero m) -> 
                well_formed_ieee754_rel mlen elen (ieee754_fp s e m) ->
                isNaN_rel (ieee754_fp s e m) b.
      
    Inductive isZero_rel : fp_format -> bool -> Prop :=
      | isZero : forall s e m b, b = (is_zero e) && (is_zero m) -> 
                 well_formed_ieee754_rel mlen elen (ieee754_fp s e m) ->
                 isZero_rel (ieee754_fp s e m) b.
 
    Inductive isNegative_rel : fp_format -> bool -> Prop :=
      | isNegative : forall s e m isnan b, isNaN_rel (ieee754_fp s e m) isnan -> b = msb s -> 
                     well_formed_ieee754_rel mlen elen (ieee754_fp s e m) ->
                     isNegative_rel (ieee754_fp s e m) (~~isnan && b).
      
    Inductive isPositive_rel : fp_format -> bool -> Prop :=
      | isPositive : forall s e m isnan b, isNaN_rel (ieee754_fp s e m) isnan -> b = ~~(msb s) -> 
                     well_formed_ieee754_rel mlen elen (ieee754_fp s e m) ->
                     isPositive_rel (ieee754_fp s e m) (~~isnan && b).
    
    Inductive abs_rel : fp_format -> fp_format -> Prop :=
      | absNaN : forall s e m, isNaN_rel (ieee754_fp s e m) true -> abs_rel (ieee754_fp s e m) (NaN mlen elen)
      | absOtherwise : forall s e m, isNaN_rel (ieee754_fp s e m) false -> 
                        abs_rel (ieee754_fp s e m) (ieee754_fp [::false] e m).
    
    Inductive neg_rel : fp_format -> fp_format -> Prop :=
      | negNaN : forall s e m, isNaN_rel (ieee754_fp s e m) true -> neg_rel (ieee754_fp s e m) (NaN mlen elen)
      | negOtherwise : forall s e m, isNaN_rel (ieee754_fp s e m) false -> 
                        neg_rel (ieee754_fp s e m) (ieee754_fp [::~~(msb s)] e m).
    
    Inductive eq_rel : fp_format -> fp_format -> Prop :=
      | eqNeitherNaN : forall bf1 bf2, (isNaN_rel bf1 false) /\ (isNaN_rel bf2 false) ->
                       forall vbf1 vbf2, (v_rel mlen elen bf1 vbf1) /\ (v_rel mlen elen bf2 vbf2)->
                        EReq_rel vbf1 vbf2 -> eq_rel bf1 bf2.
                        
    Inductive ident_rel : fp_format -> fp_format -> Prop :=
      | ident : forall bf1 bf2, forall vbf1 vbf2, (v_rel mlen elen bf1 vbf1) /\ (v_rel mlen elen bf2 vbf2)->
                  vbf1 = vbf2 -> ident_rel bf1 bf2.
                        
    Inductive leq_rel : fp_format -> fp_format -> Prop :=
      | leqNeitherNaN : forall bf1 bf2, (isNaN_rel bf1 false) /\ (isNaN_rel bf2 false) ->
                        forall vbf1 vbf2, (v_rel mlen elen bf1 vbf1) /\ (v_rel mlen elen bf2 vbf2)->
                         ERle_rel vbf1 vbf2 -> leq_rel bf1 bf2.
                         
    Inductive lt_rel : fp_format -> fp_format -> Prop :=
      | ltNeitherNaN : forall bf1 bf2, (isNaN_rel bf1 false) /\ (isNaN_rel bf2 false) ->
                        forall vbf1 vbf2, (v_rel mlen elen bf1 vbf1) /\ (v_rel mlen elen bf2 vbf2)->
                         ERlt_rel vbf1 vbf2 -> lt_rel bf1 bf2.

    Inductive geq_rel : fp_format -> fp_format -> Prop :=
      | geqNeitherNaN : forall bf1 bf2, (isNaN_rel bf1 false) /\ (isNaN_rel bf2 false) ->
                        forall vbf1 vbf2, (v_rel mlen elen bf1 vbf1) /\ (v_rel mlen elen bf2 vbf2)->
                         ERge_rel vbf1 vbf2 -> geq_rel bf1 bf2.
                         
    Inductive gt_rel : fp_format -> fp_format -> Prop :=
      | gtNeitherNaN :  forall bf1 bf2, (isNaN_rel bf1 false) /\ (isNaN_rel bf2 false) ->
                        forall vbf1 vbf2, (v_rel mlen elen bf1 vbf1) /\ (v_rel mlen elen bf2 vbf2)->
                         ERgt_rel vbf1 vbf2 -> gt_rel bf1 bf2.
      
    Inductive max_rel : fp_format -> fp_format -> fp_format -> Prop :=
      | maxGtOrRightNaN : forall bf1 bf2, (gt_rel bf1 bf2) \/ (isNaN_rel bf2 true) -> max_rel bf1 bf2 bf1
      | maxLtOrLeftNaN : forall bf1 bf2, (gt_rel bf2 bf1) \/ (isNaN_rel bf1 true) -> max_rel bf1 bf2 bf2
      | maxEq : forall bf1 bf2, (eq_rel bf1 bf2) -> max_rel bf1 bf2 bf1.
      
    Inductive min_rel : fp_format -> fp_format -> fp_format -> Prop :=
      | minLtOrLeftNaN : forall bf1 bf2, (lt_rel bf1 bf2) \/ (isNaN_rel bf2 true) -> min_rel bf1 bf2 bf1
      | minGtOrLeftNaN : forall bf1 bf2, (lt_rel bf2 bf1) \/ (isNaN_rel bf1 true) -> min_rel bf1 bf2 bf2
      | minEq : forall bf1 bf2, (eq_rel bf1 bf2) -> min_rel bf1 bf2 bf1.
    
    Definition addSign (rm : RoundingMode) (f g : fp_format) : bool :=
      match rm with
      | rtn => (sign f) || (sign g)
      | _ => (sign f) && (sign g)
      end.

    Inductive add_rel : RoundingMode -> fp_format -> fp_format -> fp_format -> Prop :=
      | add : forall f g vf vg, (v_rel mlen elen f vf) /\ (v_rel mlen elen g vg) -> 
              forall sum, ERplus_rel vf vg sum ->
              forall rm rnd_sum, rnd_rel mlen elen rm (addSign rm f g) sum rnd_sum ->
                add_rel rm f g rnd_sum.
    
    Definition subSign (rm : RoundingMode) (f g : fp_format) : bool :=
      match rm with
      | rtn => (sign f) || ~~(sign g)
      | _ => (sign f) && ~~(sign g)
      end.
      
    Inductive sub_rel : RoundingMode -> fp_format -> fp_format -> fp_format -> Prop :=
      | sub : forall f g vf vg, (v_rel mlen elen f vf) /\ (v_rel mlen elen g vg) -> 
              forall diff, ERsub_rel vf vg diff ->
              forall rm rnd_diff, rnd_rel mlen elen rm (subSign rm f g) diff rnd_diff ->
                sub_rel rm f g rnd_diff.
    
    Definition xorSign (f g : fp_format) : bool := 
      xorb (sign f) (sign g).
      
    Inductive mul_rel : RoundingMode -> fp_format -> fp_format -> fp_format -> Prop :=
      |  mul : forall f g vf vg, (v_rel mlen elen f vf) /\ (v_rel mlen elen g vg) -> 
               forall product, ERmul_rel vf vg product ->
               forall rm rnd_product, rnd_rel mlen elen rm (xorSign f g) product rnd_product ->
                 mul_rel rm f g rnd_product.

    Inductive div_rel : RoundingMode -> fp_format -> fp_format -> fp_format -> Prop :=
      |  divXorSign : forall f g, xorSign f g ->
                      forall vf vg, (v_rel mlen elen f vf) /\ (v_rel mlen elen g vg) -> 
                      forall quo, ERdiv_rel vf vg quo ->
                      forall neg_quo, ERopp_rel quo neg_quo ->
                      forall rm rnd_quo, rnd_rel mlen elen rm true neg_quo rnd_quo ->
                         div_rel rm f g rnd_quo
      |  divXnorSign : forall f g, ~~(xorSign f g) ->
                       forall vf vg, (v_rel mlen elen f vf) /\ (v_rel mlen elen g vg) -> 
                       forall quo, ERdiv_rel vf vg quo ->
                       forall rm rnd_quo, rnd_rel mlen elen rm false quo rnd_quo ->
                         div_rel rm f g rnd_quo.
      
    Inductive fma_rel : RoundingMode -> fp_format -> fp_format -> fp_format -> fp_format -> Prop :=
      |  fma : forall f g h vf vg vh, (v_rel mlen elen f vf) /\ (v_rel mlen elen g vg) /\ (v_rel mlen elen h vh) -> 
               forall product, ERmul_rel vf vg product ->
               forall sum, ERplus_rel product vh sum ->
               forall rm product_fp, mul_rel rm f g product_fp ->
               forall rnd_sum, rnd_rel mlen elen rm (addSign rm product_fp h) sum rnd_sum ->
                 fma_rel rm f g h rnd_sum.

    Inductive rem_rel : RoundingMode -> fp_format -> fp_format -> fp_format -> Prop :=
      | remRightInf : forall f g, (isNaN_rel f false) /\ (isInfinite_rel f false) /\ (isInfinite_rel g true) ->
                      forall rm, rem_rel rm f g f
      | remLeftInfOrNaN : forall f g, (isInfinite_rel f true) \/ (isNaN_rel f true) -> 
                          forall rm, rem_rel rm f g (NaN mlen elen)
      | remRightZeroOrNaN : forall f g, (isZero_rel g true) \/ (isNaN_rel g true) ->
                            forall rm, rem_rel rm f g (NaN mlen elen)
      | remOtherwise : forall f g, (isNaN_rel f false) /\ (isNaN_rel g false) /\ (isInfinite_rel f false) /\
                                     (isInfinite_rel g false) /\ (isZero_rel g false) ->
                       forall vf vg, (v_rel mlen elen f vf) /\ (v_rel mlen elen g vg) ->
                       forall quo, ERdiv_rel vf vg quo ->
                       forall rm rnd_quo, rnd_int_rel rm false quo rnd_quo ->
                       forall product, ERmul_rel vg (RN (IZR rnd_quo)) product ->
                       forall vx, ERsub_rel vf product vx ->
                       forall x, rnd_rel mlen elen rm (sign f) vx x ->
                        rem_rel rm f g x.
    
    Definition remrne_rel := rem_rel rne.

    Inductive sqrt_rel : RoundingMode -> fp_format -> fp_format -> Prop :=
      | sqrt : forall f vf, (v_rel mlen elen f vf) /\ (ERge_rel vf (RN 0)) -> 
               forall z, (ERge_rel z (RN 0)) /\ (ERmul_rel z z vf) ->
               forall rm rnd_z, rnd_rel mlen elen rm (sign f) z rnd_z ->
                sqrt_rel rm f rnd_z
      | sqrtOtherwise : forall f vf, (v_rel mlen elen f vf) ->
                        forall z, ERmul_rel z z vf ->
                          (~(ERge_rel vf (RN 0))) \/ (~(ERge_rel z (RN 0))) ->
                        forall rm, sqrt_rel rm f (NaN mlen elen).
    
    Inductive cast_rel : nat -> nat -> RoundingMode -> fp_format -> fp_format -> Prop :=
      | cast : forall f, well_formed_ieee754_rel mlen elen f ->
               forall mlen' elen' g, well_formed_ieee754_rel mlen' elen' g ->
               forall vf, v_rel mlen elen f vf ->
               forall rm, rnd_rel mlen' elen' rm (sign f) vf g ->
                cast_rel mlen' elen' rm f g.

    Inductive bitpatternToFP_rel : nat -> bits -> fp_format -> Prop :=
      | bitpatternToFP : forall n bs, (n = mlen + elen) /\ ((size bs) = n) ->
                         forall s e m, ((size s) = 1) /\ ((size e) = elen) /\ ((size m) = mlen) /\ 
                                       (bs = (m ++ e ++ s)) ->
                          ((is_zero e) /\ (is_zero m)) \/ 
                          ((is_zero e) /\ ~(is_zero m)) \/
                          (~(is_ones e) /\ ~(is_zero e)) \/
                          ((is_ones e) /\ (is_zero m)) ->
                          well_formed_ieee754_rel mlen elen (ieee754_fp s e m) ->
                           bitpatternToFP_rel n bs (ieee754_fp s e m)
      | bitpatternToFPNaN : forall n bs, (n = mlen + elen + 1) /\ ((size bs) = n) ->
                         forall s e m, ((size s) = 1) /\ ((size e) = elen) /\ ((size m) = mlen) /\ 
                                       (bs = (m ++ e ++ s)) ->
                          ~( ((is_zero e) /\ (is_zero m)) \/ 
                             ((is_zero e) /\ ~(is_zero m)) \/
                             (~(is_ones e) /\ ~(is_zero e)) \/
                             ((is_ones e) /\ (is_zero m)) ) ->
                           bitpatternToFP_rel n bs (NaN mlen elen).
    
    Inductive realToFP_rel : RoundingMode -> ExtendReal -> fp_format -> Prop :=
      | realToFP : forall rm er fp, rnd_rel mlen elen rm false er fp -> realToFP_rel rm er fp.
      
    Inductive FPToReal_rel : fp_format -> ExtendReal -> Prop :=
      | FPToReal : forall fp, well_formed_ieee754_rel mlen elen fp ->
                   forall er, v_rel mlen elen fp er -> FPToReal_rel fp er.
    
    Inductive sIntToFP_rel : RoundingMode -> bits -> fp_format -> Prop :=
      | sIntToFP : forall bs, (size bs) = (mlen + elen + 1) ->
                   forall rm fp, rnd_rel mlen elen rm false (RN (IZR (to_Z bs))) fp ->
                    sIntToFP_rel rm bs fp.
    
    Inductive uIntToFP_rel : RoundingMode -> bits -> fp_format -> Prop :=
      | uIntToFP : forall bs, (size bs) = (mlen + elen + 1) ->
                   forall rm fp, rnd_rel mlen elen rm false (RN (IZR (Z.of_nat (to_nat bs)))) fp ->
                    uIntToFP_rel rm bs fp.

    Inductive FPToSInt_rel : nat -> RoundingMode -> fp_format -> bits -> Prop :=
      | FPToSInt : forall n, n = (mlen + elen + 1) ->
                   forall f, well_formed_ieee754_rel mlen elen f ->
                   forall vf, v_rel mlen elen f vf ->
                   forall bs, (size bs) = n ->
                   forall rm, rnd_int_rel rm false vf (to_Z bs) ->
                    FPToSInt_rel n rm f bs
      | FPToSIntNaN :  forall n, n = (mlen + elen + 1) ->
                       forall f, well_formed_ieee754_rel mlen elen f ->
                       forall vf, v_rel mlen elen f vf ->
                       forall bs, (size bs) = n ->
                       forall rm, ~(rnd_int_rel rm false vf (to_Z bs)) ->
                       forall inval, (size inval) = n ->
                        FPToSInt_rel n rm f inval.
      
    Inductive FPToUInt_rel : nat -> RoundingMode -> fp_format -> bits -> Prop :=
      | FPToUInt : forall n, n = (mlen + elen + 1) ->
                   forall f, well_formed_ieee754_rel mlen elen f ->
                   forall vf, v_rel mlen elen f vf ->
                   forall bs, (size bs) = n ->
                   forall rm, rnd_int_rel rm false vf (Z.of_nat(to_nat bs)) ->
                    FPToUInt_rel n rm f bs
      | FPToUIntNaN :  forall n, n = (mlen + elen + 1) ->
                       forall f, well_formed_ieee754_rel mlen elen f ->
                       forall vf, v_rel mlen elen f vf ->
                       forall bs, (size bs) = n ->
                       forall rm, ~(rnd_int_rel rm false vf (Z.of_nat(to_nat bs))) ->
                       forall inval, (size inval) = n ->
                        FPToUInt_rel n rm f inval.
    
    (* FIXME: It is different from SMTLIB *)
    Inductive rti_rel : RoundingMode -> fp_format -> fp_format -> Prop :=
      | rtiNaN : forall f, well_formed_ieee754_rel mlen elen f ->
                   isNaN_rel f true -> forall rm, rti_rel rm f (NaN mlen elen)
      | rtiInf : forall f, well_formed_ieee754_rel mlen elen f ->
                   isInfinite_rel f true -> forall rm, rti_rel rm f f
      | rti : forall f, well_formed_ieee754_rel mlen elen f ->
              forall vf, v_rel mlen elen f vf ->
              forall rm rnd_int, rnd_int_rel rm (sign f) vf rnd_int ->
              forall rm' rnd_fp, realToFP_rel rm' (RN (IZR rnd_int)) rnd_fp ->
                rti_rel rm f rnd_fp.
    
  End Operations.

End SMTLIBfp.

Definition feunop_denote_smtlib (o : Fq2bvq.feunop) :=
  match o with
  | Fq2bvq.FUabs => SMTLIBfp.abs_rel
  | Fq2bvq.FUneg => SMTLIBfp.neg_rel
  end.
 
Definition fermunop_denote_smtlib (o : Fq2bvq.fermunop) :=
  match o with
  | Fq2bvq.FRUsqrt => SMTLIBfp.sqrt_rel
  | Fq2bvq.FRUrti => SMTLIBfp.rti_rel
  end.

Definition febinop_denote_smtlib (o : Fq2bvq.febinop) :=
  match o with
  | Fq2bvq.FBmax => SMTLIBfp.max_rel
  | Fq2bvq.FBmin => SMTLIBfp.min_rel
  | Fq2bvq.FBrem => SMTLIBfp.remrne_rel
  end.

Definition fermbinop_denote_smtlib (o : Fq2bvq.fermbinop) :=
  match o with
  | Fq2bvq.FRBadd => SMTLIBfp.add_rel
  | Fq2bvq.FRBsub => SMTLIBfp.sub_rel
  | Fq2bvq.FRBmul => SMTLIBfp.mul_rel
  | Fq2bvq.FRBdiv => SMTLIBfp.div_rel
  end.
  
Definition fermtriop_denote_smtlib (o : Fq2bvq.fermtriop) :=
  match o with
  | Fq2bvq.FRTfma => SMTLIBfp.fma_rel
  end.
  
Definition fbunop_denote_smtlib (o : Fq2bvq.fbunop) :=
  match o with
  | Fq2bvq.FUisInfinite => SMTLIBfp.isInfinite_rel
  | Fq2bvq.FUisZero => SMTLIBfp.isZero_rel 
  | Fq2bvq.FUisNaN => SMTLIBfp.isNaN_rel
  | Fq2bvq.FUisNegative => SMTLIBfp.isNegative_rel
  | Fq2bvq.FUisPositive => SMTLIBfp.isPositive_rel
  | Fq2bvq.FUisNormal => SMTLIBfp.isNormal_rel
  | Fq2bvq.FUisSubnormal => SMTLIBfp.isSubNormal_rel
  end.

Definition fbbinop_denote_smtlib (o : Fq2bvq.fbbinop) :=
  match o with
  | Fq2bvq.FBeq => SMTLIBfp.eq_rel
  | Fq2bvq.FBlt => SMTLIBfp.lt_rel
  | Fq2bvq.FBgt => SMTLIBfp.gt_rel
  | Fq2bvq.FBleq => SMTLIBfp.leq_rel
  | Fq2bvq.FBgeq => SMTLIBfp.geq_rel
  end.

Inductive eval_fp_exp : Fq2bvq.fp_exp -> SSAStore.t -> SMTLIBfp.fp_format -> nat -> nat -> Prop :=
| FEieee754 : forall elen mlen s e m st,
                eval_fp_exp (Fq2bvq.FEieee754 elen mlen s e m) st 
                  (SMTLIBfp.ieee754_fp (QFBV.eval_exp s st) (QFBV.eval_exp e st) (QFBV.eval_exp m st)) elen mlen
| FEunop : forall op fe s fp elen mlen, 
             eval_fp_exp fe s fp elen mlen ->
             forall fp', (feunop_denote_smtlib op) mlen elen fp fp' ->
             eval_fp_exp (Fq2bvq.FEunop op fe) s fp' elen mlen
| FErmunop : forall rme op fe s fp elen mlen, 
               forall rm : SMTLIBfp.RoundingMode, 
                 SMTLIBfp.bits_RM_rel (QFBV.eval_exp rme s) rm ->
                   eval_fp_exp fe s fp elen mlen ->
                   forall fp', (fermunop_denote_smtlib op) mlen elen rm fp fp' ->
                    eval_fp_exp (Fq2bvq.FErmunop op rme fe) s fp' elen mlen
| FEbinop :  forall op fe1 fe2 s fp1 fp2 elen mlen, 
               eval_fp_exp fe1 s fp1 elen mlen ->
               eval_fp_exp fe2 s fp2 elen mlen ->
                 forall fp, (febinop_denote_smtlib op) mlen elen fp1 fp2 fp->
                 eval_fp_exp (Fq2bvq.FEbinop op fe1 fe2) s fp elen mlen
| FErmbinop : forall rme op fe1 fe2 s fp1 fp2 elen mlen, 
               forall rm : SMTLIBfp.RoundingMode, 
                 SMTLIBfp.bits_RM_rel (QFBV.eval_exp rme s) rm ->
                   eval_fp_exp fe1 s fp1 elen mlen ->
                   eval_fp_exp fe2 s fp2 elen mlen ->
                     forall fp, (fermbinop_denote_smtlib op) mlen elen rm fp1 fp2 fp ->
                       eval_fp_exp (Fq2bvq.FErmbinop op rme fe1 fe2) s fp elen mlen
| FErmtriop : forall rme op fe1 fe2 fe3 s fp1 fp2 fp3 elen mlen, 
               forall rm : SMTLIBfp.RoundingMode, 
                 SMTLIBfp.bits_RM_rel (QFBV.eval_exp rme s) rm ->
                   eval_fp_exp fe1 s fp1 elen mlen ->
                   eval_fp_exp fe2 s fp2 elen mlen ->
                   eval_fp_exp fe2 s fp2 elen mlen ->
                     forall fp, (fermtriop_denote_smtlib op) mlen elen rm fp1 fp2 fp3 fp ->
                       eval_fp_exp (Fq2bvq.FErmtriop op rme fe1 fe2 fe3) s fp elen mlen
| FEofbf : forall rme fe telen tmlen s fp elen mlen, 
             forall rm : SMTLIBfp.RoundingMode, 
               SMTLIBfp.bits_RM_rel (QFBV.eval_exp rme s) rm ->
                 eval_fp_exp fe s fp elen mlen ->
                  forall fp', SMTLIBfp.cast_rel mlen elen tmlen telen rm fp fp' ->
                    eval_fp_exp (Fq2bvq.FEofbf rme fe telen tmlen) s fp' telen tmlen
| FEofbv : forall e n telen tmlen s,
             forall fp, SMTLIBfp.bitpatternToFP_rel tmlen telen n (QFBV.eval_exp e s) fp ->
               eval_fp_exp (Fq2bvq.FEofbv e n telen tmlen) s fp telen tmlen
| FEofsbv : forall rme e n telen tmlen s,
               forall rm : SMTLIBfp.RoundingMode, 
               SMTLIBfp.bits_RM_rel (QFBV.eval_exp rme s) rm ->
                  forall fp, SMTLIBfp.sIntToFP_rel tmlen telen rm (QFBV.eval_exp e s) fp ->
                    eval_fp_exp (Fq2bvq.FEofsbv rme e n telen tmlen) s fp telen tmlen
| FEofubv : forall rme e n telen tmlen s,
               forall rm : SMTLIBfp.RoundingMode, 
               SMTLIBfp.bits_RM_rel (QFBV.eval_exp rme s) rm ->
                  forall fp, SMTLIBfp.uIntToFP_rel tmlen telen rm (QFBV.eval_exp e s) fp ->
                    eval_fp_exp (Fq2bvq.FEofubv rme e n telen tmlen) s fp telen tmlen
| FEite1 : forall fb fe1 fe2 s fp1 fp2 elen mlen,
             eval_fp_bexp fb s true ->
               eval_fp_exp fe1 s fp1 elen mlen ->
               eval_fp_exp fe2 s fp2 elen mlen ->
                eval_fp_exp (Fq2bvq.FEite fb fe1 fe2) s fp1 elen mlen
 | FEite2 : forall fb fe1 fe2 s fp1 fp2 elen mlen,
             eval_fp_bexp fb s false ->
               eval_fp_exp fe1 s fp1 elen mlen ->
               eval_fp_exp fe2 s fp2 elen mlen ->
                eval_fp_exp (Fq2bvq.FEite fb fe1 fe2) s fp2 elen mlen
with
   eval_fp_bexp : Fq2bvq.fp_bexp -> SSAStore.t -> bool -> Prop :=
   | FBtrue : forall s, eval_fp_bexp Fq2bvq.FBtrue s true
   | FBfalse : forall s, eval_fp_bexp Fq2bvq.FBfalse s false
   | FBvar : forall v s b, b = QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq v (QFBV.Econst [::true])) s ->
               eval_fp_bexp (Fq2bvq.FBvar v) s b
   | FBbveq : forall fe1 fe2 s fp1 fp2 elen mlen,
                  eval_fp_exp fe1 s fp1 elen mlen ->
                  eval_fp_exp fe2 s fp2 elen mlen ->
                    forall b, reflect (SMTLIBfp.ident_rel mlen elen fp1 fp2) b ->
                      eval_fp_bexp (Fq2bvq.FBbveq fe1 fe2) s b
   | FBunop : forall op fe s fp elen mlen, 
                eval_fp_exp fe s fp elen mlen -> 
                  forall b, (fbunop_denote_smtlib op) mlen elen fp b ->  
                    eval_fp_bexp (Fq2bvq.FBunop op fe) s b
   | FBbinop : forall op fe1 fe2 s fp1 fp2 elen mlen, 
                eval_fp_exp fe1 s fp1 elen mlen -> 
                eval_fp_exp fe2 s fp2 elen mlen -> 
                   forall b, reflect ((fbbinop_denote_smtlib op) mlen elen fp1 fp2) b ->
                    eval_fp_bexp (Fq2bvq.FBbinop op fe1 fe2) s b
   | FBlneg : forall fb s b, eval_fp_bexp fb s b ->
                 eval_fp_bexp (Fq2bvq.FBlneg fb) s (~~b)
   | FBconj : forall fb1 fb2 s b1 b2, (eval_fp_bexp fb1 s b1) -> (eval_fp_bexp fb2 s b2) ->
                eval_fp_bexp (Fq2bvq.FBconj fb1 fb2) s (b1 && b2)
   | FBdisj : forall fb1 fb2 s b1 b2, (eval_fp_bexp fb1 s b1) -> (eval_fp_bexp fb2 s b2) ->
                eval_fp_bexp (Fq2bvq.FBdisj fb1 fb2) s (b1 || b2).