From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From Coq Require Import ZArith Reals.
From WordBlasting Require Import SMTLIBfpSemantics fq2bvq WBCommon WBPacking WBMain  WBWellformLemmas WBConformLemmas WBEvalesLemmas WBClassify.
From BitBlasting Require Import Typ TypEnv State QFBV AdhereConform.
From ssrlib Require Import EqVar.
From BitBlasting Require Import BBCommon.
From nbits Require Import NBits.
Require Import Lia.

Theorem word_blasting_fp_exp_flag_exclusive :
  forall (fe: Fq2bvq.fp_exp),
    forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
      Fq2bvq.well_formed_fp_exp fe te ->
        well_formed_bexps es te ->
        conformed_bexps es s te ->
        eval_bexps es s ->
          forall gen_var g' te' es' ubf wb_elen wb_mlen,
            valid_gen_var gen_var ->
              (te', g', es', ubf, wb_elen, wb_mlen) = word_blast_exp gen_var g es te fe ->
                forall s' : SSAStore.t,
                  well_formed_bexps es' te' && Fq2bvq.well_formed_unpackedbf ubf te' ->
                  conformed_bexps es' s' te' && Fq2bvq.conform_unpackedbf ubf s' te' ->
                    ((QFBV.eval_bexp (nan_flag ubf) s') = true /\ 
                     (QFBV.eval_bexp (inf_flag ubf) s') = false /\
                     (QFBV.eval_bexp (zero_flag ubf) s') = false) \/
                    ((QFBV.eval_bexp (nan_flag ubf) s') = false /\ 
                     (QFBV.eval_bexp (inf_flag ubf) s') = true /\
                     (QFBV.eval_bexp (zero_flag ubf) s') = false) \/
                    ((QFBV.eval_bexp (nan_flag ubf) s') = false /\ 
                     (QFBV.eval_bexp (inf_flag ubf) s') = false /\
                     (QFBV.eval_bexp (zero_flag ubf) s') = true) \/
                    ((QFBV.eval_bexp (nan_flag ubf) s') = false /\ 
                     (QFBV.eval_bexp (inf_flag ubf) s') = false /\
                     (QFBV.eval_bexp (zero_flag ubf) s') = false).
Proof.
Admitted.

Theorem word_blasting_fp_exp_flag_nan_exclusive :
  forall (fe: Fq2bvq.fp_exp),
    forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
      Fq2bvq.well_formed_fp_exp fe te ->
        well_formed_bexps es te ->
        conformed_bexps es s te ->
        eval_bexps es s ->
          forall gen_var g' te' es' ubf wb_elen wb_mlen,
            valid_gen_var gen_var ->
              (te', g', es', ubf, wb_elen, wb_mlen) = word_blast_exp gen_var g es te fe ->
                forall s' : SSAStore.t,
                  well_formed_bexps es' te' && Fq2bvq.well_formed_unpackedbf ubf te' ->
                  conformed_bexps es' s' te' && Fq2bvq.conform_unpackedbf ubf s' te' ->
                    (QFBV.eval_bexp (nan_flag ubf) s') = true ->
                      (QFBV.eval_bexp (inf_flag ubf) s') = false /\
                      (QFBV.eval_bexp (zero_flag ubf) s') = false.
Proof.
  move => fe te s es g Hwf Heswf Hescf Hes gen_var g' te' es' ubf wb_elen wb_mlen Hvgr wb s' Hwbwf Hwbcf HisNaN.
  move : (word_blasting_fp_exp_flag_exclusive fe te s es g Hwf Heswf Hescf Hes gen_var g' te' es' ubf wb_elen wb_mlen Hvgr wb s' Hwbwf Hwbcf) => Hflag_exclusive.
  rewrite HisNaN in Hflag_exclusive.
  inversion Hflag_exclusive.
  apply proj2 in H. auto.
  inversion H.
  apply proj1 in H0. discriminate H0.
  inversion H0.
  apply proj1 in H1. discriminate H1.
  apply proj1 in H1. discriminate H1.
Qed.

Theorem word_blasting_fp_exp_flag_inf_exclusive :
  forall (fe: Fq2bvq.fp_exp),
    forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
      Fq2bvq.well_formed_fp_exp fe te ->
        well_formed_bexps es te ->
        conformed_bexps es s te ->
        eval_bexps es s ->
          forall gen_var g' te' es' ubf wb_elen wb_mlen,
            valid_gen_var gen_var ->
              (te', g', es', ubf, wb_elen, wb_mlen) = word_blast_exp gen_var g es te fe ->
                forall s' : SSAStore.t,
                  well_formed_bexps es' te' && Fq2bvq.well_formed_unpackedbf ubf te' ->
                  conformed_bexps es' s' te' && Fq2bvq.conform_unpackedbf ubf s' te' ->
                    (QFBV.eval_bexp (inf_flag ubf) s') = true ->
                      (QFBV.eval_bexp (nan_flag ubf) s') = false /\
                      (QFBV.eval_bexp (zero_flag ubf) s') = false.
Proof.
  move => fe te s es g Hwf Heswf Hescf Hes gen_var g' te' es' ubf wb_elen wb_mlen Hvgr wb s' Hwbwf Hwbcf HisInf.
  move : (word_blasting_fp_exp_flag_exclusive fe te s es g Hwf Heswf Hescf Hes gen_var g' te' es' ubf wb_elen wb_mlen Hvgr wb s' Hwbwf Hwbcf) => Hflag_exclusive.
  rewrite HisInf in Hflag_exclusive.
  inversion Hflag_exclusive. 
  apply proj2 in H. apply proj1 in H. discriminate H.
  inversion H. 
  move : H0 => [HisNaN [Htrival HisZero]]. auto.
  inversion H0.
  apply proj2 in H1. apply proj1 in H1. discriminate H1.
  apply proj2 in H1. apply proj1 in H1. discriminate H1.
Qed.

Theorem word_blasting_fp_exp_flag_zero_exclusive :
  forall (fe: Fq2bvq.fp_exp),
    forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
      Fq2bvq.well_formed_fp_exp fe te ->
        well_formed_bexps es te ->
        conformed_bexps es s te ->
        eval_bexps es s ->
          forall gen_var g' te' es' ubf wb_elen wb_mlen,
            valid_gen_var gen_var ->
              (te', g', es', ubf, wb_elen, wb_mlen) = word_blast_exp gen_var g es te fe ->
                forall s' : SSAStore.t,
                  well_formed_bexps es' te' && Fq2bvq.well_formed_unpackedbf ubf te' ->
                  conformed_bexps es' s' te' && Fq2bvq.conform_unpackedbf ubf s' te' ->
                    (QFBV.eval_bexp (zero_flag ubf) s') = true ->
                      (QFBV.eval_bexp (nan_flag ubf) s') = false /\
                      (QFBV.eval_bexp (inf_flag ubf) s') = false.
Proof.
  move => fe te s es g Hwf Heswf Hescf Hes gen_var g' te' es' ubf wb_elen wb_mlen Hvgr wb s' Hwbwf Hwbcf HisZero.
  move : (word_blasting_fp_exp_flag_exclusive fe te s es g Hwf Heswf Hescf Hes gen_var g' te' es' ubf wb_elen wb_mlen Hvgr wb s' Hwbwf Hwbcf) => Hflag_exclusive.
  rewrite HisZero in Hflag_exclusive.
  inversion Hflag_exclusive. 
  apply proj2 in H. apply proj2 in H. discriminate H.
  inversion H. 
  apply proj2 in H0. apply proj2 in H0. discriminate H0.
  inversion H0. move : H1 => [HisNaN [HisInf Htrival]]. auto.
  apply proj2 in H1. apply proj2 in H1. discriminate H1.
Qed.

Theorem word_blasting_fp_exp_un_e_size :
  forall (fe: Fq2bvq.fp_exp),
    forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
      Fq2bvq.well_formed_fp_exp fe te ->
        well_formed_bexps es te ->
        conformed_bexps es s te ->
        eval_bexps es s ->
          forall gen_var g' te' es' ubf wb_elen wb_mlen,
            valid_gen_var gen_var ->
              (te', g', es', ubf, wb_elen, wb_mlen) = word_blast_exp gen_var g es te fe ->
                forall s' : SSAStore.t,
                  well_formed_bexps es' te' && Fq2bvq.well_formed_unpackedbf ubf te' ->
                  conformed_bexps es' s' te' && Fq2bvq.conform_unpackedbf ubf s' te' ->
                    size (QFBV.eval_exp (un_e ubf) s') = unpack_elen wb_mlen wb_elen.
Proof.
Admitted.

Theorem word_blasting_fp_exp_un_m_size :
  forall (fe: Fq2bvq.fp_exp),
    forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
      Fq2bvq.well_formed_fp_exp fe te ->
        well_formed_bexps es te ->
        conformed_bexps es s te ->
        eval_bexps es s ->
          forall gen_var g' te' es' ubf wb_elen wb_mlen,
            valid_gen_var gen_var ->
              (te', g', es', ubf, wb_elen, wb_mlen) = word_blast_exp gen_var g es te fe ->
                forall s' : SSAStore.t,
                  well_formed_bexps es' te' && Fq2bvq.well_formed_unpackedbf ubf te' ->
                  conformed_bexps es' s' te' && Fq2bvq.conform_unpackedbf ubf s' te' ->
                    size (QFBV.eval_exp (un_m ubf) s') = unpack_mlen wb_mlen.
Proof.
Admitted.

Theorem word_blasting_fp_exp_leading_one :
  forall (fe: Fq2bvq.fp_exp),
    forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
      Fq2bvq.well_formed_fp_exp fe te ->
        well_formed_bexps es te ->
        conformed_bexps es s te ->
        eval_bexps es s ->
          forall gen_var g' te' es' ubf wb_elen wb_mlen,
            valid_gen_var gen_var ->
              (te', g', es', ubf, wb_elen, wb_mlen) = word_blast_exp gen_var g es te fe ->
                forall s' : SSAStore.t,
                  well_formed_bexps es' te' && Fq2bvq.well_formed_unpackedbf ubf te' ->
                  conformed_bexps es' s' te' && Fq2bvq.conform_unpackedbf ubf s' te' ->
                    msb (QFBV.eval_exp (un_m ubf) s') = true.
Proof.
Admitted.

Theorem word_blasting_fp_exp_un_e_range :
  forall (fe: Fq2bvq.fp_exp),
    forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
      Fq2bvq.well_formed_fp_exp fe te ->
        well_formed_bexps es te ->
        conformed_bexps es s te ->
        eval_bexps es s ->
          forall gen_var g' te' es' ubf wb_elen wb_mlen,
            valid_gen_var gen_var ->
              (te', g', es', ubf, wb_elen, wb_mlen) = word_blast_exp gen_var g es te fe ->
                forall s' : SSAStore.t,
                  well_formed_bexps es' te' && Fq2bvq.well_formed_unpackedbf ubf te' ->
                  conformed_bexps es' s' te' && Fq2bvq.conform_unpackedbf ubf s' te' ->
                    (QFBV.eval_bexp (nan_flag ubf) s') = false ->
                    (QFBV.eval_bexp (zero_flag ubf) s') = false ->
                    (QFBV.eval_bexp (inf_flag ubf) s') = false ->
                      (QFBV.eval_bexp (isSuborNor_unpackedbf wb_mlen wb_elen ubf) s') = true.
Proof.
Admitted.

Lemma word_blasting_fp_exp_semantics_equivalence_ieee754 :
  forall (elen mlen : nat) (s e m : QFBV.exp),
(*     exp_constraint s && exp_constraint e && exp_constraint m -> *)
      forall (te : SSATE.env) (st : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
(*         QFBV.well_formed_exp s te && QFBV.well_formed_exp e te && QFBV.well_formed_exp m te -> *)
        Fq2bvq.well_formed_fp_exp (Fq2bvq.FEieee754 elen mlen s e m) te ->
          well_formed_bexps es te ->
          conformed_bexps es st te ->
          eval_bexps es st ->
            forall gen_var g' te' es' ubf wb_elen wb_mlen,
              valid_gen_var gen_var ->
                (te', g', es', ubf, wb_elen, wb_mlen) = word_blast_exp gen_var g es te (Fq2bvq.FEieee754 elen mlen s e m)->
                  forall st' : SSAStore.t,
                    well_formed_bexps es' te' && Fq2bvq.well_formed_unpackedbf ubf te' ->
                    conformed_bexps es' st' te' && Fq2bvq.conform_unpackedbf ubf st' te' ->
                    eval_bexps es' st' ->
                      forall pack_s pack_e pack_m, 
                        (pack_s, pack_e, pack_m) = pack wb_mlen wb_elen ubf ->
                          forall smt_s smt_e smt_m elen' mlen',
                            eval_fp_exp (Fq2bvq.FEieee754 elen mlen s e m) st (SMTLIBfp.ieee754_fp smt_s smt_e smt_m) elen' mlen' ->
                            elen' = wb_elen /\
                            mlen' = wb_mlen /\
                            smt_s = (QFBV.eval_exp pack_s st') /\ 
                            smt_e = (QFBV.eval_exp pack_e st') /\ 
                            smt_m = (QFBV.eval_exp pack_m st').
Proof.
Admitted.

Section EUnop.

Lemma word_blasting_fp_exp_semantics_equivalence_abs :
  forall (fe : Fq2bvq.fp_exp),
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_exp fe te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1,
            valid_gen_var gen_var ->
              (te1, g1, es1, ubf1, wb_elen1, wb_mlen1) = word_blast_exp gen_var g0 es0 te0 fe ->
                  forall s1 : SSAStore.t,
                    well_formed_bexps es1 te1 && Fq2bvq.well_formed_unpackedbf ubf1 te1 ->
                    conformed_bexps es1 s1 te1 && Fq2bvq.conform_unpackedbf ubf1 s1 te1 ->
                    eval_bexps es1 s1 ->
                      forall pack_s1 pack_e1 pack_m1, 
                        (pack_s1, pack_e1, pack_m1) = pack wb_mlen1 wb_elen1 ubf1 ->
                          forall smt_s1 smt_e1 smt_m1 elen1 mlen1,
                            eval_fp_exp fe s0 (SMTLIBfp.ieee754_fp smt_s1 smt_e1 smt_m1) elen1 mlen1 ->
                            elen1 = wb_elen1 /\
                            mlen1 = wb_mlen1 /\
                            smt_s1 = (QFBV.eval_exp pack_s1 s1) /\ 
                            smt_e1 = (QFBV.eval_exp pack_e1 s1) /\ 
                            smt_m1 = (QFBV.eval_exp pack_m1 s1)) ->
      forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
        Fq2bvq.well_formed_fp_exp (Fq2bvq.FEunop Fq2bvq.FUabs fe) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' ubf wb_elen wb_mlen,
              valid_gen_var gen_var ->
                (te', g', es', ubf, wb_elen, wb_mlen) = word_blast_exp gen_var g es te (Fq2bvq.FEunop Fq2bvq.FUabs fe)->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && Fq2bvq.well_formed_unpackedbf ubf te' ->
                    conformed_bexps es' s' te' && Fq2bvq.conform_unpackedbf ubf s' te' ->
                    eval_bexps es' s' ->
                      forall pack_s pack_e pack_m, 
                        (pack_s, pack_e, pack_m) = pack wb_mlen wb_elen ubf ->
                          (forall smt_s smt_e smt_m elen mlen,
                            eval_fp_exp (Fq2bvq.FEunop Fq2bvq.FUabs fe) s (SMTLIBfp.ieee754_fp smt_s smt_e smt_m) elen mlen ->
                            elen = wb_elen /\
                            mlen = wb_mlen /\
                            smt_s = (QFBV.eval_exp pack_s s') /\ 
                            smt_e = (QFBV.eval_exp pack_e s') /\ 
                            smt_m = (QFBV.eval_exp pack_m s')).
Proof.
  move => fe IH te s es g /= Hwf Heswf Hescf Hes gen_var g' te' es' ubf wb_elen wb_mlen Hgv wb s' Hwbwf Hwbcf Hes' pack_s pack_e pack_m Hpack smt_s smt_e smt_m elen mlen Hsmt.
  case Hwb: (word_blast_exp gen_var g es te fe) => [[[[[te1 g1] es1] ubf1] wb_elen1] wb_mlen1].
  rewrite Hwb in wb. inversion wb. symmetry in Hwb.
  inversion Hwf.
  specialize (IH te s es g H3 Heswf Hescf Hes gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb).
  
  move : (word_blasting_fp_exp_is_wellformed fe te es g H3 Heswf gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb) => Hwbwf1.
  move : (word_blasting_fp_exp_is_conformed fe te s es g H3 Heswf Hescf gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb Hwbwf1) => Hwbcf1.
  destruct Hwbcf1 as [s1 Hwbcf1].
  move : (word_blasting_fp_exp_eval_es fe te s es g H3 Heswf Hescf Hes gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb s1 Hwbwf1 Hwbcf1) => Hes1.
  specialize (IH s1 Hwbwf1 Hwbcf1 Hes1).
  case Hpack1: (pack wb_mlen1 wb_elen1 ubf1) => [[pack_s1 pack_e1] pack_m1]. symmetry in Hpack1.
  specialize (IH pack_s1 pack_e1 pack_m1 Hpack1).
  inversion Hsmt. subst. inversion H10. subst.
  {
    specialize (IH s0 e m elen mlen H5). inversion IH.
    assert (Helen : elen = wb_elen1). apply IH.
    assert (Hmlen : mlen = wb_mlen1). apply IH.
    assert (Hs : s0 = QFBV.eval_exp pack_s1 s1). apply IH.
    assert (He : e = QFBV.eval_exp pack_e1 s1). apply IH.
    assert (Hm : m = QFBV.eval_exp pack_m1 s1). apply IH.
    split. apply Helen. split. apply Hmlen. 
    inversion H2. inversion Hpack. simpl. inversion Hpack1. simpl.
    unfold WBAbsNeg.abs_unpackedbf in H0. unfold make_exp_var in H0. 
    assert (Hnan_flag : nan_flag ubf = nan_flag ubf1). 
    {
      case Hgv1 : (gen_var g1) => [v2 g2]. rewrite Hgv1 in H0.
      case Hgv2 : (gen_var g2) => [v3 g3]. rewrite Hgv2 in H0.
      inversion H0. reflexivity. 
    }
    assert (Hinf_flag : inf_flag ubf = Eite_bexp (nan_flag ubf1) QFBV.Bfalse (inf_flag ubf1)).
    {
      case Hgv1 : (gen_var g1) => [v2 g2]. rewrite Hgv1 in H0.
      case Hgv2 : (gen_var g2) => [v3 g3]. rewrite Hgv2 in H0.
      inversion H0. reflexivity. 
    }
    assert (Hzero_flag : zero_flag ubf = Eite_bexp (nan_flag ubf1) QFBV.Bfalse (zero_flag ubf1)). 
    {
      case Hgv1 : (gen_var g1) => [v2 g2]. rewrite Hgv1 in H0.
      case Hgv2 : (gen_var g2) => [v3 g3]. rewrite Hgv2 in H0.
      inversion H0. reflexivity. 
    }
    assert (Hun_s : un_s ubf = Eite_bexp (nan_flag ubf1) QFBV.Btrue QFBV.Bfalse).
    {
      case Hgv1 : (gen_var g1) => [v2 g2]. rewrite Hgv1 in H0.
      case Hgv2 : (gen_var g2) => [v3 g3]. rewrite Hgv2 in H0.
      inversion H0. reflexivity. 
    }
    assert (Hun_e : QFBV.eval_exp (un_e ubf) s' = QFBV.eval_exp (QFBV.Eite (nan_flag ubf1) (defaultExponent wb_mlen1 wb_elen1) (un_e ubf1)) s').
    {
      case Hgv1 : (gen_var g1) => [v2 g2]. rewrite Hgv1 in H0.
      case Hgv2 : (gen_var g2) => [v3 g3]. rewrite Hgv2 in H0.
      inversion H0. simpl. 
      rewrite H21 in Hes'. 
      unfold eval_bexps in Hes'. 
      rewrite -cat1s in Hes'. rewrite all_cat in Hes'. 

      assert (Hes'' : all (eval_bexp_forseq s')
         [:: QFBV.Bbinop QFBV.Beq (QFBV.Evar v3)
               (QFBV.Eite (nan_flag ubf1)
                  (defaultSignificand wb_mlen1) 
                  (un_m ubf1))] &&
       all (eval_bexp_forseq s')
         (QFBV.Bbinop QFBV.Beq (QFBV.Evar v2)
            (QFBV.Eite (nan_flag ubf1)
               (defaultExponent wb_mlen1 wb_elen1) 
               (un_e ubf1)) :: es1) = true). auto.
      apply Bools.and_true_r in Hes''.
      rewrite -cat1s in Hes''. rewrite all_cat in Hes''. 
      apply Bools.and_true_l in Hes''. 
      simpl in Hes''. simpl. 
      apply Bools.and_true_l in Hes''.
      move : Hes'' => /eqP Hes''. exact Hes''.
    }
    assert (Hun_m :  QFBV.eval_exp (un_m ubf) s' =  QFBV.eval_exp (QFBV.Eite (nan_flag ubf1) (defaultSignificand wb_mlen1) (un_m ubf1)) s'). 
    {
      case Hgv1 : (gen_var g1) => [v2 g2]. rewrite Hgv1 in H0.
      case Hgv2 : (gen_var g2) => [v3 g3]. rewrite Hgv2 in H0.
      inversion H0. simpl. 
      rewrite H21 in Hes'. 
      unfold eval_bexps in Hes'. 
      rewrite -cat1s in Hes'. rewrite all_cat in Hes'. 

      assert (Hes'' : all (eval_bexp_forseq s')
         [:: QFBV.Bbinop QFBV.Beq (QFBV.Evar v3)
               (QFBV.Eite (nan_flag ubf1)
                  (defaultSignificand wb_mlen1) 
                  (un_m ubf1))] &&
       all (eval_bexp_forseq s')
         (QFBV.Bbinop QFBV.Beq (QFBV.Evar v2)
            (QFBV.Eite (nan_flag ubf1)
               (defaultExponent wb_mlen1 wb_elen1) 
               (un_e ubf1)) :: es1) = true). auto.
      apply Bools.and_true_l in Hes''.
      rewrite -cat1s in Hes''. rewrite all_cat in Hes''. 
      apply Bools.and_true_l in Hes''. 
      simpl in Hes''. simpl. 
      apply Bools.and_true_l in Hes''.
      move : Hes'' => /eqP Hes''. exact Hes''.
    }
    
    assert (Hnan_flag' : QFBV.eval_bexp (nan_flag ubf1) s' = QFBV.eval_bexp (nan_flag ubf1) s1). admit.
    assert (Hzero_flag' : QFBV.eval_bexp (zero_flag ubf1) s' = QFBV.eval_bexp (zero_flag ubf1) s1). admit.
    assert (Hinf_flag' : QFBV.eval_bexp (inf_flag ubf1) s' = QFBV.eval_bexp (inf_flag ubf1) s1). admit.
    assert (Hun_s' : QFBV.eval_bexp (un_s ubf1) s' = QFBV.eval_bexp (un_s ubf1) s1). admit.
    assert (Hun_e' : QFBV.eval_exp (un_e ubf1) s' = QFBV.eval_exp (un_e ubf1) s1). admit.
    assert (Hun_m' : QFBV.eval_exp (un_m ubf1) s' = QFBV.eval_exp (un_m ubf1) s1). admit. 
    
    rewrite Hnan_flag Hun_s Hun_e Hun_m Hnan_flag'. simpl.
    
    case HisNaN : (QFBV.eval_bexp (nan_flag ubf1) s1).
    + simpl. rewrite Helen Hmlen. auto.
    + rewrite H17 in He. simpl in He. rewrite HisNaN in He. simpl in He.
      rewrite H18 in Hm. simpl in Hm. rewrite HisNaN in Hm. simpl in Hm.
      case HisInf : (QFBV.eval_bexp (inf_flag ubf1) s1).
      - rewrite HisInf in He. simpl in He. rewrite HisInf in Hm. simpl in Hm.
        rewrite He Hm zeros_is_zero ones_is_ones in H9. simpl in H9. discriminate H9.
      - rewrite HisInf in He. simpl in He. rewrite HisInf in Hm. simpl in Hm.
        case HisZero : (QFBV.eval_bexp (zero_flag ubf1) s1).
        * rewrite HisZero in He. simpl in He. rewrite HisZero in Hm. simpl in Hm.
          rewrite He Hm zeros_is_zero Bool.andb_false_r in H9. simpl in H9. discriminate H9.
        * rewrite HisZero in He. simpl in He. rewrite HisZero in Hm. simpl in Hm.
          assert (Hcontra : is_ones e = false).
          {
            rewrite He.
            case Hnormal : 
             (sleB
              (sext (unpack_elen wb_mlen1 wb_elen1 - unpack_elen wb_mlen1 wb_elen1)
                 (unpack_elen wb_mlen1 wb_elen1) -bits of Z (min_normal_e wb_elen1)%bits)
              (QFBV.eval_exp (un_e ubf1) s1) &&
            sleB (QFBV.eval_exp (un_e ubf1) s1)
              (sext (unpack_elen wb_mlen1 wb_elen1 - unpack_elen wb_mlen1 wb_elen1)
                 (unpack_elen wb_mlen1 wb_elen1) -bits of Z (max_normal_e wb_elen1)%bits)).
            {
              admit. (* copy proof of isNaN *)
            }
            {
              assert (is_ones_zeros_false : forall n, n > 0 -> is_ones (zeros n) = false).
              + destruct n. auto. auto.
              apply is_ones_zeros_false.
              rewrite -H. inversion H11. auto.
            }
          }
          rewrite Hcontra in H9. discriminate H9.
  }
  {
      rewrite -H1 in H5.
      specialize (IH s0 e m elen mlen H5). inversion IH.
      assert (Helen : elen = wb_elen1). apply IH.
      assert (Hmlen : mlen = wb_mlen1). apply IH.
      assert (Hs : s0 = QFBV.eval_exp pack_s1 s1). apply IH.
      assert (He : e = QFBV.eval_exp pack_e1 s1). apply IH.
      assert (Hm : m = QFBV.eval_exp pack_m1 s1). apply IH.
      split. apply Helen. split. apply Hmlen. 
      inversion H2. inversion Hpack. simpl. inversion Hpack1. simpl.
      unfold WBAbsNeg.abs_unpackedbf in H0. unfold make_exp_var in H0. 
      assert (Hnan_flag : nan_flag ubf = nan_flag ubf1). 
      {
        case Hgv1 : (gen_var g1) => [v2 g2]. rewrite Hgv1 in H0.
        case Hgv2 : (gen_var g2) => [v3 g3]. rewrite Hgv2 in H0.
        inversion H0. reflexivity. 
      }
      assert (Hinf_flag : inf_flag ubf = Eite_bexp (nan_flag ubf1) QFBV.Bfalse (inf_flag ubf1)).
      {
        case Hgv1 : (gen_var g1) => [v2 g2]. rewrite Hgv1 in H0.
        case Hgv2 : (gen_var g2) => [v3 g3]. rewrite Hgv2 in H0.
        inversion H0. reflexivity. 
      }
      assert (Hzero_flag : zero_flag ubf = Eite_bexp (nan_flag ubf1) QFBV.Bfalse (zero_flag ubf1)). 
      {
        case Hgv1 : (gen_var g1) => [v2 g2]. rewrite Hgv1 in H0.
        case Hgv2 : (gen_var g2) => [v3 g3]. rewrite Hgv2 in H0.
        inversion H0. reflexivity. 
      }
      assert (Hun_s : un_s ubf = Eite_bexp (nan_flag ubf1) QFBV.Btrue QFBV.Bfalse).
      {
        case Hgv1 : (gen_var g1) => [v2 g2]. rewrite Hgv1 in H0.
        case Hgv2 : (gen_var g2) => [v3 g3]. rewrite Hgv2 in H0.
        inversion H0. reflexivity. 
      }
      assert (Hun_e : QFBV.eval_exp (un_e ubf) s' = QFBV.eval_exp (QFBV.Eite (nan_flag ubf1) (defaultExponent wb_mlen1 wb_elen1) (un_e ubf1)) s').
      {
        case Hgv1 : (gen_var g1) => [v2 g2]. rewrite Hgv1 in H0.
        case Hgv2 : (gen_var g2) => [v3 g3]. rewrite Hgv2 in H0.
        inversion H0. simpl. 
        rewrite H25 in Hes'. 
        unfold eval_bexps in Hes'. 
        rewrite -cat1s in Hes'. rewrite all_cat in Hes'. 

        assert (Hes'' : all (eval_bexp_forseq s')
           [:: QFBV.Bbinop QFBV.Beq (QFBV.Evar v3)
                 (QFBV.Eite (nan_flag ubf1)
                    (defaultSignificand wb_mlen1) 
                    (un_m ubf1))] &&
         all (eval_bexp_forseq s')
           (QFBV.Bbinop QFBV.Beq (QFBV.Evar v2)
              (QFBV.Eite (nan_flag ubf1)
                 (defaultExponent wb_mlen1 wb_elen1) 
                 (un_e ubf1)) :: es1) = true). auto.
        apply Bools.and_true_r in Hes''.
        rewrite -cat1s in Hes''. rewrite all_cat in Hes''. 
        apply Bools.and_true_l in Hes''. 
        simpl in Hes''. simpl. 
        apply Bools.and_true_l in Hes''.
        move : Hes'' => /eqP Hes''. exact Hes''.
      }
      assert (Hun_m :  QFBV.eval_exp (un_m ubf) s' =  QFBV.eval_exp (QFBV.Eite (nan_flag ubf1) (defaultSignificand wb_mlen1) (un_m ubf1)) s'). 
      {
        case Hgv1 : (gen_var g1) => [v2 g2]. rewrite Hgv1 in H0.
        case Hgv2 : (gen_var g2) => [v3 g3]. rewrite Hgv2 in H0.
        inversion H0. simpl. 
        rewrite H25 in Hes'. 
        unfold eval_bexps in Hes'. 
        rewrite -cat1s in Hes'. rewrite all_cat in Hes'. 

        assert (Hes'' : all (eval_bexp_forseq s')
           [:: QFBV.Bbinop QFBV.Beq (QFBV.Evar v3)
                 (QFBV.Eite (nan_flag ubf1)
                    (defaultSignificand wb_mlen1) 
                    (un_m ubf1))] &&
         all (eval_bexp_forseq s')
           (QFBV.Bbinop QFBV.Beq (QFBV.Evar v2)
              (QFBV.Eite (nan_flag ubf1)
                 (defaultExponent wb_mlen1 wb_elen1) 
                 (un_e ubf1)) :: es1) = true). auto.
        apply Bools.and_true_l in Hes''.
        rewrite -cat1s in Hes''. rewrite all_cat in Hes''. 
        apply Bools.and_true_l in Hes''. 
        simpl in Hes''. simpl. 
        apply Bools.and_true_l in Hes''.
        move : Hes'' => /eqP Hes''. exact Hes''.
      }

      assert (Hnan_flag' : QFBV.eval_bexp (nan_flag ubf1) s' = QFBV.eval_bexp (nan_flag ubf1) s1). admit.
      assert (Hzero_flag' : QFBV.eval_bexp (zero_flag ubf1) s' = QFBV.eval_bexp (zero_flag ubf1) s1). admit.
      assert (Hinf_flag' : QFBV.eval_bexp (inf_flag ubf1) s' = QFBV.eval_bexp (inf_flag ubf1) s1). admit.
      assert (Hun_s' : QFBV.eval_bexp (un_s ubf1) s' = QFBV.eval_bexp (un_s ubf1) s1). admit.
      assert (Hun_e' : QFBV.eval_exp (un_e ubf1) s' = QFBV.eval_exp (un_e ubf1) s1). admit.
      assert (Hun_m' : QFBV.eval_exp (un_m ubf1) s' = QFBV.eval_exp (un_m ubf1) s1). admit.
        
      simpl. 
      case Hif1 : (unpack_elen wb_mlen1 wb_elen1 <= unpack_mlen wb_mlen1). simpl.
      {
        rewrite Hnan_flag Hinf_flag Hzero_flag Hun_s Hun_e Hun_m Hnan_flag'. simpl.
       case HisNaN : (QFBV.eval_bexp (nan_flag ubf1) s1). simpl.
        + rewrite H4 H21 in He. rewrite H6 H22 in Hm. simpl in He. simpl in Hm.
          rewrite HisNaN in He. rewrite HisNaN in Hm. simpl in He. simpl in Hm.
          rewrite He Hm in H14. rewrite ones_is_ones in H14.
          assert (is_zero_ones_false : forall n, n > 0 -> is_zero (ones n) = false). 
          { destruct n. auto. auto. }
          rewrite is_zero_ones_false in H14. simpl in H14. discriminate H14.
          inversion H15. rewrite Hmlen in H24. auto.
        + rewrite Hnan_flag' HisNaN. simpl. rewrite Hinf_flag' Hzero_flag'.
          case HisInf : (QFBV.eval_bexp (inf_flag ubf1) s1). simpl.
          - rewrite -H4 -H6 He Hm H21 H22. simpl. rewrite HisNaN HisInf. simpl. auto.
          - simpl. case HisZero : (QFBV.eval_bexp (zero_flag ubf1) s1).
            * rewrite -H4 -H6 He Hm H21 H22. simpl. rewrite HisNaN HisInf HisZero. simpl. auto.
            * rewrite -H4 -H6 He Hm H21 H22. simpl. rewrite HisNaN HisInf HisZero. simpl.
              split. auto. split. rewrite Hun_e'. reflexivity.
              rewrite Hif1. rewrite Hun_e' Hun_m'. reflexivity.
       }
       { 
         simpl. rewrite Hnan_flag Hinf_flag Hzero_flag Hun_s Hun_e Hun_m Hnan_flag'. simpl.
         case HisNaN : (QFBV.eval_bexp (nan_flag ubf1) s1). simpl.
          + rewrite H4 H21 in He. rewrite H6 H22 in Hm. simpl in He. simpl in Hm.
            rewrite HisNaN in He. rewrite HisNaN in Hm. simpl in He. simpl in Hm.
            rewrite He Hm in H14. rewrite ones_is_ones in H14.
            assert (is_zero_ones_false : forall n, n > 0 -> is_zero (ones n) = false). 
            { destruct n. auto. auto. }
            rewrite is_zero_ones_false in H14. simpl in H14. discriminate H14.
            inversion H15. rewrite Hmlen in H24. auto.
          + rewrite Hnan_flag' HisNaN. simpl. rewrite Hinf_flag' Hzero_flag'.
            case HisInf : (QFBV.eval_bexp (inf_flag ubf1) s1). simpl.
            - rewrite -H4 -H6 He Hm H21 H22. simpl. rewrite HisNaN HisInf. simpl. auto.
            - simpl. case HisZero : (QFBV.eval_bexp (zero_flag ubf1) s1).
              * rewrite -H4 -H6 He Hm H21 H22. simpl. rewrite HisNaN HisInf HisZero. simpl. auto.
              * rewrite -H4 -H6 He Hm H21 H22. simpl. rewrite HisNaN HisInf HisZero. simpl.
                split. auto. split. rewrite Hun_e'. reflexivity.
                rewrite Hif1. rewrite Hun_e' Hun_m'. reflexivity.
        }
   }
Admitted.

Lemma word_blasting_fp_exp_semantics_equivalence_neg :
  forall (fe : Fq2bvq.fp_exp),
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_exp fe te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1,
            valid_gen_var gen_var ->
              (te1, g1, es1, ubf1, wb_elen1, wb_mlen1) = word_blast_exp gen_var g0 es0 te0 fe ->
                  forall s1 : SSAStore.t,
                    well_formed_bexps es1 te1 && Fq2bvq.well_formed_unpackedbf ubf1 te1 ->
                    conformed_bexps es1 s1 te1 && Fq2bvq.conform_unpackedbf ubf1 s1 te1 ->
                    eval_bexps es1 s1 ->
                      forall pack_s1 pack_e1 pack_m1, 
                        (pack_s1, pack_e1, pack_m1) = pack wb_mlen1 wb_elen1 ubf1 ->
                          forall smt_s1 smt_e1 smt_m1 elen1 mlen1,
                            eval_fp_exp fe s0 (SMTLIBfp.ieee754_fp smt_s1 smt_e1 smt_m1) elen1 mlen1 ->
                            elen1 = wb_elen1 /\
                            mlen1 = wb_mlen1 /\
                            smt_s1 = (QFBV.eval_exp pack_s1 s1) /\ 
                            smt_e1 = (QFBV.eval_exp pack_e1 s1) /\ 
                            smt_m1 = (QFBV.eval_exp pack_m1 s1)) ->
      forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
        Fq2bvq.well_formed_fp_exp (Fq2bvq.FEunop Fq2bvq.FUneg fe) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' ubf wb_elen wb_mlen,
              valid_gen_var gen_var ->
                (te', g', es', ubf, wb_elen, wb_mlen) = word_blast_exp gen_var g es te (Fq2bvq.FEunop Fq2bvq.FUneg fe)->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && Fq2bvq.well_formed_unpackedbf ubf te' ->
                    conformed_bexps es' s' te' && Fq2bvq.conform_unpackedbf ubf s' te' ->
                    eval_bexps es' s' ->
                      forall pack_s pack_e pack_m, 
                        (pack_s, pack_e, pack_m) = pack wb_mlen wb_elen ubf ->
                          (forall smt_s smt_e smt_m elen mlen,
                            eval_fp_exp (Fq2bvq.FEunop Fq2bvq.FUneg fe) s (SMTLIBfp.ieee754_fp smt_s smt_e smt_m) elen mlen ->
                            elen = wb_elen /\
                            mlen = wb_mlen /\
                            smt_s = (QFBV.eval_exp pack_s s') /\ 
                            smt_e = (QFBV.eval_exp pack_e s') /\ 
                            smt_m = (QFBV.eval_exp pack_m s')).
Proof.
  move => fe IH te s es g /= Hwf Heswf Hescf Hes gen_var g' te' es' ubf wb_elen wb_mlen Hgv wb s' Hwbwf Hwbcf Hes' pack_s pack_e pack_m Hpack smt_s smt_e smt_m elen mlen Hsmt.
  case Hwb: (word_blast_exp gen_var g es te fe) => [[[[[te1 g1] es1] ubf1] wb_elen1] wb_mlen1].
  rewrite Hwb in wb. inversion wb. symmetry in Hwb.
  inversion Hwf.
  specialize (IH te s es g H3 Heswf Hescf Hes gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb).
  
  move : (word_blasting_fp_exp_is_wellformed fe te es g H3 Heswf gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb) => Hwbwf1.
  move : (word_blasting_fp_exp_is_conformed fe te s es g H3 Heswf Hescf gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb Hwbwf1) => Hwbcf1.
  destruct Hwbcf1 as [s1 Hwbcf1].
  move : (word_blasting_fp_exp_eval_es fe te s es g H3 Heswf Hescf Hes gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb s1 Hwbwf1 Hwbcf1) => Hes1.
  specialize (IH s1 Hwbwf1 Hwbcf1 Hes1).
  case Hpack1: (pack wb_mlen1 wb_elen1 ubf1) => [[pack_s1 pack_e1] pack_m1]. symmetry in Hpack1.
  specialize (IH pack_s1 pack_e1 pack_m1 Hpack1).
  inversion Hsmt. subst. inversion H10. subst.
  {
    specialize (IH s0 e m elen mlen H5). inversion IH.
    assert (Helen : elen = wb_elen1). apply IH.
    assert (Hmlen : mlen = wb_mlen1). apply IH.
    assert (Hs : s0 = QFBV.eval_exp pack_s1 s1). apply IH.
    assert (He : e = QFBV.eval_exp pack_e1 s1). apply IH.
    assert (Hm : m = QFBV.eval_exp pack_m1 s1). apply IH.
    split. apply Helen. split. apply Hmlen. 
    inversion H2. inversion Hpack. simpl. inversion Hpack1. simpl.
    unfold WBAbsNeg.neg_unpackedbf in H0. unfold make_exp_var in H0. 
    assert (Hnan_flag : nan_flag ubf = nan_flag ubf1). 
    {
      case Hgv1 : (gen_var g1) => [v2 g2]. rewrite Hgv1 in H0.
      case Hgv2 : (gen_var g2) => [v3 g3]. rewrite Hgv2 in H0.
      inversion H0. reflexivity. 
    }
    assert (Hinf_flag : inf_flag ubf = Eite_bexp (nan_flag ubf1) QFBV.Bfalse (inf_flag ubf1)).
    {
      case Hgv1 : (gen_var g1) => [v2 g2]. rewrite Hgv1 in H0.
      case Hgv2 : (gen_var g2) => [v3 g3]. rewrite Hgv2 in H0.
      inversion H0. reflexivity. 
    }
    assert (Hzero_flag : zero_flag ubf = Eite_bexp (nan_flag ubf1) QFBV.Bfalse (zero_flag ubf1)). 
    {
      case Hgv1 : (gen_var g1) => [v2 g2]. rewrite Hgv1 in H0.
      case Hgv2 : (gen_var g2) => [v3 g3]. rewrite Hgv2 in H0.
      inversion H0. reflexivity. 
    }
    assert (Hun_s : un_s ubf = Eite_bexp (nan_flag ubf1) QFBV.Btrue (QFBV.Blneg (un_s ubf1))).
    {
      case Hgv1 : (gen_var g1) => [v2 g2]. rewrite Hgv1 in H0.
      case Hgv2 : (gen_var g2) => [v3 g3]. rewrite Hgv2 in H0.
      inversion H0. reflexivity. 
    }
    assert (Hun_e : QFBV.eval_exp (un_e ubf) s' = QFBV.eval_exp (QFBV.Eite (nan_flag ubf1) (defaultExponent wb_mlen1 wb_elen1) (un_e ubf1)) s').
    {
      case Hgv1 : (gen_var g1) => [v2 g2]. rewrite Hgv1 in H0.
      case Hgv2 : (gen_var g2) => [v3 g3]. rewrite Hgv2 in H0.
      inversion H0. simpl. 
      rewrite H21 in Hes'. 
      unfold eval_bexps in Hes'. 
      rewrite -cat1s in Hes'. rewrite all_cat in Hes'. 

      assert (Hes'' : all (eval_bexp_forseq s')
         [:: QFBV.Bbinop QFBV.Beq (QFBV.Evar v3)
               (QFBV.Eite (nan_flag ubf1)
                  (defaultSignificand wb_mlen1) 
                  (un_m ubf1))] &&
       all (eval_bexp_forseq s')
         (QFBV.Bbinop QFBV.Beq (QFBV.Evar v2)
            (QFBV.Eite (nan_flag ubf1)
               (defaultExponent wb_mlen1 wb_elen1) 
               (un_e ubf1)) :: es1) = true). auto.
      apply Bools.and_true_r in Hes''.
      rewrite -cat1s in Hes''. rewrite all_cat in Hes''. 
      apply Bools.and_true_l in Hes''. 
      simpl in Hes''. simpl. 
      apply Bools.and_true_l in Hes''.
      move : Hes'' => /eqP Hes''. exact Hes''.
    }
    assert (Hun_m :  QFBV.eval_exp (un_m ubf) s' =  QFBV.eval_exp (QFBV.Eite (nan_flag ubf1) (defaultSignificand wb_mlen1) (un_m ubf1)) s'). 
    {
      case Hgv1 : (gen_var g1) => [v2 g2]. rewrite Hgv1 in H0.
      case Hgv2 : (gen_var g2) => [v3 g3]. rewrite Hgv2 in H0.
      inversion H0. simpl. 
      rewrite H21 in Hes'. 
      unfold eval_bexps in Hes'. 
      rewrite -cat1s in Hes'. rewrite all_cat in Hes'. 

      assert (Hes'' : all (eval_bexp_forseq s')
         [:: QFBV.Bbinop QFBV.Beq (QFBV.Evar v3)
               (QFBV.Eite (nan_flag ubf1)
                  (defaultSignificand wb_mlen1) 
                  (un_m ubf1))] &&
       all (eval_bexp_forseq s')
         (QFBV.Bbinop QFBV.Beq (QFBV.Evar v2)
            (QFBV.Eite (nan_flag ubf1)
               (defaultExponent wb_mlen1 wb_elen1) 
               (un_e ubf1)) :: es1) = true). auto.
      apply Bools.and_true_l in Hes''.
      rewrite -cat1s in Hes''. rewrite all_cat in Hes''. 
      apply Bools.and_true_l in Hes''. 
      simpl in Hes''. simpl. 
      apply Bools.and_true_l in Hes''.
      move : Hes'' => /eqP Hes''. exact Hes''.
    }
    
    assert (Hnan_flag' : QFBV.eval_bexp (nan_flag ubf1) s' = QFBV.eval_bexp (nan_flag ubf1) s1). admit.
    assert (Hzero_flag' : QFBV.eval_bexp (zero_flag ubf1) s' = QFBV.eval_bexp (zero_flag ubf1) s1). admit.
    assert (Hinf_flag' : QFBV.eval_bexp (inf_flag ubf1) s' = QFBV.eval_bexp (inf_flag ubf1) s1). admit.
    assert (Hun_s' : QFBV.eval_bexp (un_s ubf1) s' = QFBV.eval_bexp (un_s ubf1) s1). admit.
    assert (Hun_e' : QFBV.eval_exp (un_e ubf1) s' = QFBV.eval_exp (un_e ubf1) s1). admit.
    assert (Hun_m' : QFBV.eval_exp (un_m ubf1) s' = QFBV.eval_exp (un_m ubf1) s1). admit. 
    
    rewrite Hnan_flag Hun_s Hun_e Hun_m Hnan_flag'. simpl.
    
    case HisNaN : (QFBV.eval_bexp (nan_flag ubf1) s1).
    + simpl. rewrite Helen Hmlen. auto.
    + rewrite H17 in He. simpl in He. rewrite HisNaN in He. simpl in He.
      rewrite H18 in Hm. simpl in Hm. rewrite HisNaN in Hm. simpl in Hm.
      case HisInf : (QFBV.eval_bexp (inf_flag ubf1) s1).
      - rewrite HisInf in He. simpl in He. rewrite HisInf in Hm. simpl in Hm.
        rewrite He Hm zeros_is_zero ones_is_ones in H9. simpl in H9. discriminate H9.
      - rewrite HisInf in He. simpl in He. rewrite HisInf in Hm. simpl in Hm.
        case HisZero : (QFBV.eval_bexp (zero_flag ubf1) s1).
        * rewrite HisZero in He. simpl in He. rewrite HisZero in Hm. simpl in Hm.
          rewrite He Hm zeros_is_zero Bool.andb_false_r in H9. simpl in H9. discriminate H9.
        * rewrite HisZero in He. simpl in He. rewrite HisZero in Hm. simpl in Hm.
          assert (Hcontra : is_ones e = false).
          {
            rewrite He.
            case Hnormal : 
             (sleB
              (sext (unpack_elen wb_mlen1 wb_elen1 - unpack_elen wb_mlen1 wb_elen1)
                 (unpack_elen wb_mlen1 wb_elen1) -bits of Z (min_normal_e wb_elen1)%bits)
              (QFBV.eval_exp (un_e ubf1) s1) &&
            sleB (QFBV.eval_exp (un_e ubf1) s1)
              (sext (unpack_elen wb_mlen1 wb_elen1 - unpack_elen wb_mlen1 wb_elen1)
                 (unpack_elen wb_mlen1 wb_elen1) -bits of Z (max_normal_e wb_elen1)%bits)).
            {
              admit. (* copy proof of isNaN *)
            }
            {
              assert (is_ones_zeros_false : forall n, n > 0 -> is_ones (zeros n) = false).
              + destruct n. auto. auto.
              apply is_ones_zeros_false.
              rewrite -H. inversion H11. auto.
            }
          }
          rewrite Hcontra in H9. discriminate H9.
  }
  {
      rewrite -H1 in H5.
      specialize (IH s0 e m elen mlen H5). inversion IH.
      assert (Helen : elen = wb_elen1). apply IH.
      assert (Hmlen : mlen = wb_mlen1). apply IH.
      assert (Hs : s0 = QFBV.eval_exp pack_s1 s1). apply IH.
      assert (He : e = QFBV.eval_exp pack_e1 s1). apply IH.
      assert (Hm : m = QFBV.eval_exp pack_m1 s1). apply IH.
      split. apply Helen. split. apply Hmlen. 
      inversion H2. inversion Hpack. simpl. inversion Hpack1. simpl.
      unfold WBAbsNeg.neg_unpackedbf in H0. unfold make_exp_var in H0. 
      assert (Hnan_flag : nan_flag ubf = nan_flag ubf1). 
      {
        case Hgv1 : (gen_var g1) => [v2 g2]. rewrite Hgv1 in H0.
        case Hgv2 : (gen_var g2) => [v3 g3]. rewrite Hgv2 in H0.
        inversion H0. reflexivity. 
      }
      assert (Hinf_flag : inf_flag ubf = Eite_bexp (nan_flag ubf1) QFBV.Bfalse (inf_flag ubf1)).
      {
        case Hgv1 : (gen_var g1) => [v2 g2]. rewrite Hgv1 in H0.
        case Hgv2 : (gen_var g2) => [v3 g3]. rewrite Hgv2 in H0.
        inversion H0. reflexivity. 
      }
      assert (Hzero_flag : zero_flag ubf = Eite_bexp (nan_flag ubf1) QFBV.Bfalse (zero_flag ubf1)). 
      {
        case Hgv1 : (gen_var g1) => [v2 g2]. rewrite Hgv1 in H0.
        case Hgv2 : (gen_var g2) => [v3 g3]. rewrite Hgv2 in H0.
        inversion H0. reflexivity. 
      }
      assert (Hun_s : un_s ubf = Eite_bexp (nan_flag ubf1) QFBV.Btrue (QFBV.Blneg (un_s ubf1))).
      {
        case Hgv1 : (gen_var g1) => [v2 g2]. rewrite Hgv1 in H0.
        case Hgv2 : (gen_var g2) => [v3 g3]. rewrite Hgv2 in H0.
        inversion H0. reflexivity. 
      }
      assert (Hun_e : QFBV.eval_exp (un_e ubf) s' = QFBV.eval_exp (QFBV.Eite (nan_flag ubf1) (defaultExponent wb_mlen1 wb_elen1) (un_e ubf1)) s').
      {
        case Hgv1 : (gen_var g1) => [v2 g2]. rewrite Hgv1 in H0.
        case Hgv2 : (gen_var g2) => [v3 g3]. rewrite Hgv2 in H0.
        inversion H0. simpl. 
        rewrite H25 in Hes'. 
        unfold eval_bexps in Hes'. 
        rewrite -cat1s in Hes'. rewrite all_cat in Hes'. 

        assert (Hes'' : all (eval_bexp_forseq s')
           [:: QFBV.Bbinop QFBV.Beq (QFBV.Evar v3)
                 (QFBV.Eite (nan_flag ubf1)
                    (defaultSignificand wb_mlen1) 
                    (un_m ubf1))] &&
         all (eval_bexp_forseq s')
           (QFBV.Bbinop QFBV.Beq (QFBV.Evar v2)
              (QFBV.Eite (nan_flag ubf1)
                 (defaultExponent wb_mlen1 wb_elen1) 
                 (un_e ubf1)) :: es1) = true). auto.
        apply Bools.and_true_r in Hes''.
        rewrite -cat1s in Hes''. rewrite all_cat in Hes''. 
        apply Bools.and_true_l in Hes''. 
        simpl in Hes''. simpl. 
        apply Bools.and_true_l in Hes''.
        move : Hes'' => /eqP Hes''. exact Hes''.
      }
      assert (Hun_m :  QFBV.eval_exp (un_m ubf) s' =  QFBV.eval_exp (QFBV.Eite (nan_flag ubf1) (defaultSignificand wb_mlen1) (un_m ubf1)) s'). 
      {
        case Hgv1 : (gen_var g1) => [v2 g2]. rewrite Hgv1 in H0.
        case Hgv2 : (gen_var g2) => [v3 g3]. rewrite Hgv2 in H0.
        inversion H0. simpl. 
        rewrite H25 in Hes'. 
        unfold eval_bexps in Hes'. 
        rewrite -cat1s in Hes'. rewrite all_cat in Hes'. 

        assert (Hes'' : all (eval_bexp_forseq s')
           [:: QFBV.Bbinop QFBV.Beq (QFBV.Evar v3)
                 (QFBV.Eite (nan_flag ubf1)
                    (defaultSignificand wb_mlen1) 
                    (un_m ubf1))] &&
         all (eval_bexp_forseq s')
           (QFBV.Bbinop QFBV.Beq (QFBV.Evar v2)
              (QFBV.Eite (nan_flag ubf1)
                 (defaultExponent wb_mlen1 wb_elen1) 
                 (un_e ubf1)) :: es1) = true). auto.
        apply Bools.and_true_l in Hes''.
        rewrite -cat1s in Hes''. rewrite all_cat in Hes''. 
        apply Bools.and_true_l in Hes''. 
        simpl in Hes''. simpl. 
        apply Bools.and_true_l in Hes''.
        move : Hes'' => /eqP Hes''. exact Hes''.
      }

      assert (Hnan_flag' : QFBV.eval_bexp (nan_flag ubf1) s' = QFBV.eval_bexp (nan_flag ubf1) s1). admit.
      assert (Hzero_flag' : QFBV.eval_bexp (zero_flag ubf1) s' = QFBV.eval_bexp (zero_flag ubf1) s1). admit.
      assert (Hinf_flag' : QFBV.eval_bexp (inf_flag ubf1) s' = QFBV.eval_bexp (inf_flag ubf1) s1). admit.
      assert (Hun_s' : QFBV.eval_bexp (un_s ubf1) s' = QFBV.eval_bexp (un_s ubf1) s1). admit.
      assert (Hun_e' : QFBV.eval_exp (un_e ubf1) s' = QFBV.eval_exp (un_e ubf1) s1). admit.
      assert (Hun_m' : QFBV.eval_exp (un_m ubf1) s' = QFBV.eval_exp (un_m ubf1) s1). admit.
        
      simpl. 
      case Hif1 : (unpack_elen wb_mlen1 wb_elen1 <= unpack_mlen wb_mlen1). simpl.
      {
        rewrite Hnan_flag Hinf_flag Hzero_flag Hun_s Hun_e Hun_m Hnan_flag'. simpl.
       case HisNaN : (QFBV.eval_bexp (nan_flag ubf1) s1). simpl.
        + rewrite H4 H21 in He. rewrite H6 H22 in Hm. simpl in He. simpl in Hm.
          rewrite HisNaN in He. rewrite HisNaN in Hm. simpl in He. simpl in Hm.
          rewrite He Hm in H14. rewrite ones_is_ones in H14.
          assert (is_zero_ones_false : forall n, n > 0 -> is_zero (ones n) = false). 
          { destruct n. auto. auto. }
          rewrite is_zero_ones_false in H14. simpl in H14. discriminate H14.
          inversion H15. rewrite Hmlen in H24. auto.
        + rewrite Hnan_flag' HisNaN. simpl. rewrite Hinf_flag' Hzero_flag' Hun_s'.
          case HisInf : (QFBV.eval_bexp (inf_flag ubf1) s1). simpl.
          - rewrite -H4 -H6 He Hm H21 H22. simpl. rewrite HisNaN HisInf. simpl.
            rewrite Hs H20. simpl. rewrite HisNaN.
            destruct (QFBV.eval_bexp (un_s ubf1) s1). auto. auto.
          - simpl. case HisZero : (QFBV.eval_bexp (zero_flag ubf1) s1).
            * rewrite Hs H20. simpl. rewrite HisNaN.
              destruct (QFBV.eval_bexp (un_s ubf1) s1). 
              rewrite -H4 -H6 He Hm H21 H22. simpl. rewrite HisNaN HisInf HisZero. simpl. auto.
              rewrite -H4 -H6 He Hm H21 H22. simpl. rewrite HisNaN HisInf HisZero. simpl. auto.
            * rewrite Hs H20. simpl. rewrite HisNaN.
              destruct (QFBV.eval_bexp (un_s ubf1) s1).
              rewrite -H4 -H6 He Hm H21 H22. simpl. rewrite HisNaN HisInf HisZero. simpl.
              split. auto. split. rewrite Hun_e'. reflexivity.
              rewrite Hif1. rewrite Hun_e' Hun_m'. reflexivity.
              rewrite -H4 -H6 He Hm H21 H22. simpl. rewrite HisNaN HisInf HisZero. simpl.
              split. auto. split. rewrite Hun_e'. reflexivity.
              rewrite Hif1. rewrite Hun_e' Hun_m'. reflexivity.
       }
       { 
         simpl. rewrite Hnan_flag Hinf_flag Hzero_flag Hun_s Hun_e Hun_m Hnan_flag'. simpl.
         case HisNaN : (QFBV.eval_bexp (nan_flag ubf1) s1). simpl.
          + rewrite H4 H21 in He. rewrite H6 H22 in Hm. simpl in He. simpl in Hm.
            rewrite HisNaN in He. rewrite HisNaN in Hm. simpl in He. simpl in Hm.
            rewrite He Hm in H14. rewrite ones_is_ones in H14.
            assert (is_zero_ones_false : forall n, n > 0 -> is_zero (ones n) = false). 
            { destruct n. auto. auto. }
            rewrite is_zero_ones_false in H14. simpl in H14. discriminate H14.
            inversion H15. rewrite Hmlen in H24. auto.
          + rewrite Hnan_flag' HisNaN. simpl. rewrite Hinf_flag' Hzero_flag' Hun_s'.
            rewrite Hs H20. simpl. rewrite HisNaN.
            case HisInf : (QFBV.eval_bexp (inf_flag ubf1) s1). simpl.
            - rewrite -H4 -H6 He Hm H21 H22. simpl. rewrite HisNaN HisInf. simpl.
              destruct (QFBV.eval_bexp (un_s ubf1) s1). 
              simpl. auto. simpl. auto.
            - simpl. case HisZero : (QFBV.eval_bexp (zero_flag ubf1) s1).
              * rewrite -H4 -H6 He Hm H21 H22. simpl. rewrite HisNaN HisInf HisZero. simpl.
                destruct (QFBV.eval_bexp (un_s ubf1) s1). 
                simpl. auto. simpl. auto.
              * rewrite -H4 -H6 He Hm H21 H22. simpl. rewrite HisNaN HisInf HisZero. simpl.
                split. 
                destruct (QFBV.eval_bexp (un_s ubf1) s1). 
                simpl. auto. simpl. auto.
                split. rewrite Hun_e'. reflexivity.
                rewrite Hif1. rewrite Hun_e' Hun_m'. reflexivity.
        }
   }
Admitted.

Lemma word_blasting_fp_exp_semantics_equivalence_unop :
  forall (op : Fq2bvq.feunop) (fe : Fq2bvq.fp_exp),
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_exp fe te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1,
            valid_gen_var gen_var ->
              (te1, g1, es1, ubf1, wb_elen1, wb_mlen1) = word_blast_exp gen_var g0 es0 te0 fe ->
                  forall s1 : SSAStore.t,
                    well_formed_bexps es1 te1 && Fq2bvq.well_formed_unpackedbf ubf1 te1 ->
                    conformed_bexps es1 s1 te1 && Fq2bvq.conform_unpackedbf ubf1 s1 te1 ->
                    eval_bexps es1 s1 ->
                      forall pack_s1 pack_e1 pack_m1, 
                        (pack_s1, pack_e1, pack_m1) = pack wb_mlen1 wb_elen1 ubf1 ->
                          forall smt_s1 smt_e1 smt_m1 elen1 mlen1,
                            eval_fp_exp fe s0 (SMTLIBfp.ieee754_fp smt_s1 smt_e1 smt_m1) elen1 mlen1 ->
                            elen1 = wb_elen1 /\
                            mlen1 = wb_mlen1 /\
                            smt_s1 = (QFBV.eval_exp pack_s1 s1) /\ 
                            smt_e1 = (QFBV.eval_exp pack_e1 s1) /\ 
                            smt_m1 = (QFBV.eval_exp pack_m1 s1)) ->
      forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
        Fq2bvq.well_formed_fp_exp (Fq2bvq.FEunop op fe) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' ubf wb_elen wb_mlen,
              valid_gen_var gen_var ->
                (te', g', es', ubf, wb_elen, wb_mlen) = word_blast_exp gen_var g es te (Fq2bvq.FEunop op fe)->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && Fq2bvq.well_formed_unpackedbf ubf te' ->
                    conformed_bexps es' s' te' && Fq2bvq.conform_unpackedbf ubf s' te' ->
                    eval_bexps es' s' ->
                      forall pack_s pack_e pack_m, 
                        (pack_s, pack_e, pack_m) = pack wb_mlen wb_elen ubf ->
                          (forall smt_s smt_e smt_m elen mlen,
                            eval_fp_exp (Fq2bvq.FEunop op fe) s (SMTLIBfp.ieee754_fp smt_s smt_e smt_m) elen mlen ->
                            elen = wb_elen /\
                            mlen = wb_mlen /\
                            smt_s = (QFBV.eval_exp pack_s s') /\ 
                            smt_e = (QFBV.eval_exp pack_e s') /\ 
                            smt_m = (QFBV.eval_exp pack_m s')).
Proof.
Admitted.

End EUnop.

Section ERMUnop.

Lemma word_blasting_fp_exp_semantics_equivalence_sqrt :
  forall (rm : QFBV.exp) (fe : Fq2bvq.fp_exp),
(*     exp_constraint rm -> *)
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_exp fe te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1,
            valid_gen_var gen_var ->
              (te1, g1, es1, ubf1, wb_elen1, wb_mlen1) = word_blast_exp gen_var g0 es0 te0 fe ->
                  forall s1 : SSAStore.t,
                    well_formed_bexps es1 te1 && Fq2bvq.well_formed_unpackedbf ubf1 te1 ->
                    conformed_bexps es1 s1 te1 && Fq2bvq.conform_unpackedbf ubf1 s1 te1 ->
                    eval_bexps es1 s1 ->
                      forall pack_s1 pack_e1 pack_m1, 
                        (pack_s1, pack_e1, pack_m1) = pack wb_mlen1 wb_elen1 ubf1 ->
                          forall smt_s1 smt_e1 smt_m1 elen1 mlen1,
                            eval_fp_exp fe s0 (SMTLIBfp.ieee754_fp smt_s1 smt_e1 smt_m1) elen1 mlen1 ->
                            elen1 = wb_elen1 /\
                            mlen1 = wb_mlen1 /\
                            smt_s1 = (QFBV.eval_exp pack_s1 s1) /\ 
                            smt_e1 = (QFBV.eval_exp pack_e1 s1) /\ 
                            smt_m1 = (QFBV.eval_exp pack_m1 s1)) -> 
      forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
        Fq2bvq.well_formed_fp_exp (Fq2bvq.FErmunop Fq2bvq.FRUsqrt rm fe) te  ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' ubf wb_elen wb_mlen,
              valid_gen_var gen_var ->
                (te', g', es', ubf, wb_elen, wb_mlen) = word_blast_exp gen_var g es te (Fq2bvq.FErmunop Fq2bvq.FRUsqrt rm fe)->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && Fq2bvq.well_formed_unpackedbf ubf te' ->
                    conformed_bexps es' s' te' && Fq2bvq.conform_unpackedbf ubf s' te' ->
                    eval_bexps es' s' ->
                      forall pack_s pack_e pack_m, 
                        (pack_s, pack_e, pack_m) = pack wb_mlen wb_elen ubf ->
                          (forall smt_s smt_e smt_m elen mlen,
                            eval_fp_exp (Fq2bvq.FErmunop Fq2bvq.FRUsqrt rm fe) s (SMTLIBfp.ieee754_fp smt_s smt_e smt_m) elen mlen ->
                            elen = wb_elen /\
                            mlen = wb_mlen /\
                            smt_s = (QFBV.eval_exp pack_s s') /\ 
                            smt_e = (QFBV.eval_exp pack_e s') /\ 
                            smt_m = (QFBV.eval_exp pack_m s')).
Proof.
Admitted.

Lemma word_blasting_fp_exp_semantics_equivalence_rti :
  forall (rm : QFBV.exp) (fe : Fq2bvq.fp_exp),
(*     exp_constraint rm -> *)
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_exp fe te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1,
            valid_gen_var gen_var ->
              (te1, g1, es1, ubf1, wb_elen1, wb_mlen1) = word_blast_exp gen_var g0 es0 te0 fe ->
                  forall s1 : SSAStore.t,
                    well_formed_bexps es1 te1 && Fq2bvq.well_formed_unpackedbf ubf1 te1 ->
                    conformed_bexps es1 s1 te1 && Fq2bvq.conform_unpackedbf ubf1 s1 te1 ->
                    eval_bexps es1 s1 ->
                      forall pack_s1 pack_e1 pack_m1, 
                        (pack_s1, pack_e1, pack_m1) = pack wb_mlen1 wb_elen1 ubf1 ->
                          forall smt_s1 smt_e1 smt_m1 elen1 mlen1,
                            eval_fp_exp fe s0 (SMTLIBfp.ieee754_fp smt_s1 smt_e1 smt_m1) elen1 mlen1 ->
                            elen1 = wb_elen1 /\
                            mlen1 = wb_mlen1 /\
                            smt_s1 = (QFBV.eval_exp pack_s1 s1) /\ 
                            smt_e1 = (QFBV.eval_exp pack_e1 s1) /\ 
                            smt_m1 = (QFBV.eval_exp pack_m1 s1)) -> 
      forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
        Fq2bvq.well_formed_fp_exp (Fq2bvq.FErmunop Fq2bvq.FRUrti rm fe) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' ubf wb_elen wb_mlen,
              valid_gen_var gen_var ->
                (te', g', es', ubf, wb_elen, wb_mlen) = word_blast_exp gen_var g es te (Fq2bvq.FErmunop Fq2bvq.FRUrti rm fe)->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && Fq2bvq.well_formed_unpackedbf ubf te' ->
                    conformed_bexps es' s' te' && Fq2bvq.conform_unpackedbf ubf s' te' ->
                    eval_bexps es' s' ->
                      forall pack_s pack_e pack_m, 
                        (pack_s, pack_e, pack_m) = pack wb_mlen wb_elen ubf ->
                          (forall smt_s smt_e smt_m elen mlen,
                            eval_fp_exp (Fq2bvq.FErmunop Fq2bvq.FRUrti rm fe) s (SMTLIBfp.ieee754_fp smt_s smt_e smt_m) elen mlen ->
                            elen = wb_elen /\
                            mlen = wb_mlen /\
                            smt_s = (QFBV.eval_exp pack_s s') /\ 
                            smt_e = (QFBV.eval_exp pack_e s') /\ 
                            smt_m = (QFBV.eval_exp pack_m s')).
Proof.
Admitted.

Lemma word_blasting_fp_exp_semantics_equivalence_rmunop :
  forall (op : Fq2bvq.fermunop) (rm : QFBV.exp) (fe : Fq2bvq.fp_exp),
(*     exp_constraint rm -> *)
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_exp fe te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1,
            valid_gen_var gen_var ->
              (te1, g1, es1, ubf1, wb_elen1, wb_mlen1) = word_blast_exp gen_var g0 es0 te0 fe ->
                  forall s1 : SSAStore.t,
                    well_formed_bexps es1 te1 && Fq2bvq.well_formed_unpackedbf ubf1 te1 ->
                    conformed_bexps es1 s1 te1 && Fq2bvq.conform_unpackedbf ubf1 s1 te1 ->
                    eval_bexps es1 s1 ->
                      forall pack_s1 pack_e1 pack_m1, 
                        (pack_s1, pack_e1, pack_m1) = pack wb_mlen1 wb_elen1 ubf1 ->
                          forall smt_s1 smt_e1 smt_m1 elen1 mlen1,
                            eval_fp_exp fe s0 (SMTLIBfp.ieee754_fp smt_s1 smt_e1 smt_m1) elen1 mlen1 ->
                            elen1 = wb_elen1 /\
                            mlen1 = wb_mlen1 /\
                            smt_s1 = (QFBV.eval_exp pack_s1 s1) /\ 
                            smt_e1 = (QFBV.eval_exp pack_e1 s1) /\ 
                            smt_m1 = (QFBV.eval_exp pack_m1 s1)) -> 
      forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
        Fq2bvq.well_formed_fp_exp (Fq2bvq.FErmunop op rm fe) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' ubf wb_elen wb_mlen,
              valid_gen_var gen_var ->
                (te', g', es', ubf, wb_elen, wb_mlen) = word_blast_exp gen_var g es te (Fq2bvq.FErmunop op rm fe)->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && Fq2bvq.well_formed_unpackedbf ubf te' ->
                    conformed_bexps es' s' te' && Fq2bvq.conform_unpackedbf ubf s' te' ->
                    eval_bexps es' s' ->
                      forall pack_s pack_e pack_m, 
                        (pack_s, pack_e, pack_m) = pack wb_mlen wb_elen ubf ->
                          (forall smt_s smt_e smt_m elen mlen,
                            eval_fp_exp (Fq2bvq.FErmunop op rm fe) s (SMTLIBfp.ieee754_fp smt_s smt_e smt_m) elen mlen ->
                            elen = wb_elen /\
                            mlen = wb_mlen /\
                            smt_s = (QFBV.eval_exp pack_s s') /\ 
                            smt_e = (QFBV.eval_exp pack_e s') /\ 
                            smt_m = (QFBV.eval_exp pack_m s')).
Proof.
Admitted.

End ERMUnop.

Section EBinop.

Lemma word_blasting_fp_exp_semantics_equivalence_max :
  forall (fe1 : Fq2bvq.fp_exp) (fe2 : Fq2bvq.fp_exp),
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_exp fe1 te0 ->
      Fq2bvq.well_formed_fp_exp fe2 te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1,
            valid_gen_var gen_var ->
              (te1, g1, es1, ubf1, wb_elen1, wb_mlen1) = word_blast_exp gen_var g0 es0 te0 fe1 ->
                forall s1 : SSAStore.t,
                  well_formed_bexps es1 te1 && Fq2bvq.well_formed_unpackedbf ubf1 te1 ->
                  conformed_bexps es1 s1 te1 && Fq2bvq.conform_unpackedbf ubf1 s1 te1 ->
                  eval_bexps es1 s1 ->
                    forall pack_s1 pack_e1 pack_m1, 
                      (pack_s1, pack_e1, pack_m1) = pack wb_mlen1 wb_elen1 ubf1 ->
                        forall smt_s1 smt_e1 smt_m1 elen1 mlen1,
                          eval_fp_exp fe1 s0 (SMTLIBfp.ieee754_fp smt_s1 smt_e1 smt_m1) elen1 mlen1 ->
          forall g2 te2 es2 ubf2 wb_elen2 wb_mlen2,
              (te2, g2, es2, ubf2, wb_elen2, wb_mlen2) = word_blast_exp gen_var g1 es1 te1 fe2 ->
                forall s2 : SSAStore.t,
                  well_formed_bexps es2 te2 && Fq2bvq.well_formed_unpackedbf ubf2 te2 ->
                  conformed_bexps es2 s2 te2 && Fq2bvq.conform_unpackedbf ubf2 s2 te2 ->
                  eval_bexps es2 s2 ->
                    forall pack_s2 pack_e2 pack_m2, 
                      (pack_s2, pack_e2, pack_m2) = pack wb_mlen2 wb_elen2 ubf2 ->
                        forall smt_s2 smt_e2 smt_m2 elen2 mlen2,
                          eval_fp_exp fe2 s0 (SMTLIBfp.ieee754_fp smt_s2 smt_e2 smt_m2) elen2 mlen2 ->
                            (elen1 = wb_elen1 /\
                            mlen1 = wb_mlen1 /\
                            smt_s1 = (QFBV.eval_exp pack_s1 s1) /\ 
                            smt_e1 = (QFBV.eval_exp pack_e1 s1) /\ 
                            smt_m1 = (QFBV.eval_exp pack_m1 s1)) /\ 
                            (elen2 = wb_elen2 /\
                            mlen2 = wb_mlen2 /\
                            smt_s2 = (QFBV.eval_exp pack_s2 s2) /\ 
                            smt_e2 = (QFBV.eval_exp pack_e2 s2) /\ 
                            smt_m2 = (QFBV.eval_exp pack_m2 s2))) -> 
      forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
        Fq2bvq.well_formed_fp_exp (Fq2bvq.FEbinop Fq2bvq.FBmax fe1 fe2) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' ubf wb_elen wb_mlen,
              valid_gen_var gen_var ->
                (te', g', es', ubf, wb_elen, wb_mlen) = word_blast_exp gen_var g es te (Fq2bvq.FEbinop Fq2bvq.FBmax fe1 fe2)->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && Fq2bvq.well_formed_unpackedbf ubf te' ->
                    conformed_bexps es' s' te' && Fq2bvq.conform_unpackedbf ubf s' te' ->
                    eval_bexps es' s' ->
                      forall pack_s pack_e pack_m, 
                        (pack_s, pack_e, pack_m) = pack wb_mlen wb_elen ubf ->
                          (forall smt_s smt_e smt_m elen mlen,
                            eval_fp_exp  (Fq2bvq.FEbinop Fq2bvq.FBmax fe1 fe2) s (SMTLIBfp.ieee754_fp smt_s smt_e smt_m) elen mlen ->
                            elen = wb_elen /\
                            mlen = wb_mlen /\
                            smt_s = (QFBV.eval_exp pack_s s') /\ 
                            smt_e = (QFBV.eval_exp pack_e s') /\ 
                            smt_m = (QFBV.eval_exp pack_m s')).
Proof.
Admitted.

Lemma word_blasting_fp_exp_semantics_equivalence_min :
  forall (fe1 : Fq2bvq.fp_exp) (fe2 : Fq2bvq.fp_exp),
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_exp fe1 te0 ->
      Fq2bvq.well_formed_fp_exp fe2 te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1,
            valid_gen_var gen_var ->
              (te1, g1, es1, ubf1, wb_elen1, wb_mlen1) = word_blast_exp gen_var g0 es0 te0 fe1 ->
                forall s1 : SSAStore.t,
                  well_formed_bexps es1 te1 && Fq2bvq.well_formed_unpackedbf ubf1 te1 ->
                  conformed_bexps es1 s1 te1 && Fq2bvq.conform_unpackedbf ubf1 s1 te1 ->
                  eval_bexps es1 s1 ->
                    forall pack_s1 pack_e1 pack_m1, 
                      (pack_s1, pack_e1, pack_m1) = pack wb_mlen1 wb_elen1 ubf1 ->
                        forall smt_s1 smt_e1 smt_m1 elen1 mlen1,
                          eval_fp_exp fe1 s0 (SMTLIBfp.ieee754_fp smt_s1 smt_e1 smt_m1) elen1 mlen1 ->
          forall g2 te2 es2 ubf2 wb_elen2 wb_mlen2,
              (te2, g2, es2, ubf2, wb_elen2, wb_mlen2) = word_blast_exp gen_var g1 es1 te1 fe2 ->
                forall s2 : SSAStore.t,
                  well_formed_bexps es2 te2 && Fq2bvq.well_formed_unpackedbf ubf2 te2 ->
                  conformed_bexps es2 s2 te2 && Fq2bvq.conform_unpackedbf ubf2 s2 te2 ->
                  eval_bexps es2 s2 ->
                    forall pack_s2 pack_e2 pack_m2, 
                      (pack_s2, pack_e2, pack_m2) = pack wb_mlen2 wb_elen2 ubf2 ->
                        forall smt_s2 smt_e2 smt_m2 elen2 mlen2,
                          eval_fp_exp fe2 s0 (SMTLIBfp.ieee754_fp smt_s2 smt_e2 smt_m2) elen2 mlen2 ->
                            (elen1 = wb_elen1 /\
                            mlen1 = wb_mlen1 /\
                            smt_s1 = (QFBV.eval_exp pack_s1 s1) /\ 
                            smt_e1 = (QFBV.eval_exp pack_e1 s1) /\ 
                            smt_m1 = (QFBV.eval_exp pack_m1 s1)) /\ 
                            (elen2 = wb_elen2 /\
                            mlen2 = wb_mlen2 /\
                            smt_s2 = (QFBV.eval_exp pack_s2 s2) /\ 
                            smt_e2 = (QFBV.eval_exp pack_e2 s2) /\ 
                            smt_m2 = (QFBV.eval_exp pack_m2 s2))) -> 
      forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
        Fq2bvq.well_formed_fp_exp (Fq2bvq.FEbinop Fq2bvq.FBmin fe1 fe2) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' ubf wb_elen wb_mlen,
              valid_gen_var gen_var ->
                (te', g', es', ubf, wb_elen, wb_mlen) = word_blast_exp gen_var g es te (Fq2bvq.FEbinop Fq2bvq.FBmin fe1 fe2)->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && Fq2bvq.well_formed_unpackedbf ubf te' ->
                    conformed_bexps es' s' te' && Fq2bvq.conform_unpackedbf ubf s' te' ->
                    eval_bexps es' s' ->
                      forall pack_s pack_e pack_m, 
                        (pack_s, pack_e, pack_m) = pack wb_mlen wb_elen ubf ->
                          (forall smt_s smt_e smt_m elen mlen,
                            eval_fp_exp  (Fq2bvq.FEbinop Fq2bvq.FBmin fe1 fe2) s (SMTLIBfp.ieee754_fp smt_s smt_e smt_m) elen mlen ->
                            elen = wb_elen /\
                            mlen = wb_mlen /\
                            smt_s = (QFBV.eval_exp pack_s s') /\ 
                            smt_e = (QFBV.eval_exp pack_e s') /\ 
                            smt_m = (QFBV.eval_exp pack_m s')).
Proof.
Admitted.

Lemma word_blasting_fp_exp_semantics_equivalence_rem :
  forall (fe1 : Fq2bvq.fp_exp) (fe2 : Fq2bvq.fp_exp),
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_exp fe1 te0 ->
      Fq2bvq.well_formed_fp_exp fe2 te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1,
            valid_gen_var gen_var ->
              (te1, g1, es1, ubf1, wb_elen1, wb_mlen1) = word_blast_exp gen_var g0 es0 te0 fe1 ->
                forall s1 : SSAStore.t,
                  well_formed_bexps es1 te1 && Fq2bvq.well_formed_unpackedbf ubf1 te1 ->
                  conformed_bexps es1 s1 te1 && Fq2bvq.conform_unpackedbf ubf1 s1 te1 ->
                  eval_bexps es1 s1 ->
                    forall pack_s1 pack_e1 pack_m1, 
                      (pack_s1, pack_e1, pack_m1) = pack wb_mlen1 wb_elen1 ubf1 ->
                        forall smt_s1 smt_e1 smt_m1 elen1 mlen1,
                          eval_fp_exp fe1 s0 (SMTLIBfp.ieee754_fp smt_s1 smt_e1 smt_m1) elen1 mlen1 ->
          forall g2 te2 es2 ubf2 wb_elen2 wb_mlen2,
              (te2, g2, es2, ubf2, wb_elen2, wb_mlen2) = word_blast_exp gen_var g1 es1 te1 fe2 ->
                forall s2 : SSAStore.t,
                  well_formed_bexps es2 te2 && Fq2bvq.well_formed_unpackedbf ubf2 te2 ->
                  conformed_bexps es2 s2 te2 && Fq2bvq.conform_unpackedbf ubf2 s2 te2 ->
                  eval_bexps es2 s2 ->
                    forall pack_s2 pack_e2 pack_m2, 
                      (pack_s2, pack_e2, pack_m2) = pack wb_mlen2 wb_elen2 ubf2 ->
                        forall smt_s2 smt_e2 smt_m2 elen2 mlen2,
                          eval_fp_exp fe2 s0 (SMTLIBfp.ieee754_fp smt_s2 smt_e2 smt_m2) elen2 mlen2 ->
                            (elen1 = wb_elen1 /\
                            mlen1 = wb_mlen1 /\
                            smt_s1 = (QFBV.eval_exp pack_s1 s1) /\ 
                            smt_e1 = (QFBV.eval_exp pack_e1 s1) /\ 
                            smt_m1 = (QFBV.eval_exp pack_m1 s1)) /\ 
                            (elen2 = wb_elen2 /\
                            mlen2 = wb_mlen2 /\
                            smt_s2 = (QFBV.eval_exp pack_s2 s2) /\ 
                            smt_e2 = (QFBV.eval_exp pack_e2 s2) /\ 
                            smt_m2 = (QFBV.eval_exp pack_m2 s2))) -> 
      forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
        Fq2bvq.well_formed_fp_exp (Fq2bvq.FEbinop Fq2bvq.FBrem fe1 fe2) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' ubf wb_elen wb_mlen,
              valid_gen_var gen_var ->
                (te', g', es', ubf, wb_elen, wb_mlen) = word_blast_exp gen_var g es te (Fq2bvq.FEbinop Fq2bvq.FBrem fe1 fe2)->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && Fq2bvq.well_formed_unpackedbf ubf te' ->
                    conformed_bexps es' s' te' && Fq2bvq.conform_unpackedbf ubf s' te' ->
                    eval_bexps es' s' ->
                      forall pack_s pack_e pack_m, 
                        (pack_s, pack_e, pack_m) = pack wb_mlen wb_elen ubf ->
                          (forall smt_s smt_e smt_m elen mlen,
                            eval_fp_exp  (Fq2bvq.FEbinop Fq2bvq.FBrem fe1 fe2) s (SMTLIBfp.ieee754_fp smt_s smt_e smt_m) elen mlen ->
                            elen = wb_elen /\
                            mlen = wb_mlen /\
                            smt_s = (QFBV.eval_exp pack_s s') /\ 
                            smt_e = (QFBV.eval_exp pack_e s') /\ 
                            smt_m = (QFBV.eval_exp pack_m s')).
Proof.
Admitted.

Lemma word_blasting_fp_exp_semantics_equivalence_binop :
  forall (op : Fq2bvq.febinop) (fe1 : Fq2bvq.fp_exp) (fe2 : Fq2bvq.fp_exp),
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_exp fe1 te0 ->
      Fq2bvq.well_formed_fp_exp fe2 te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1,
            valid_gen_var gen_var ->
              (te1, g1, es1, ubf1, wb_elen1, wb_mlen1) = word_blast_exp gen_var g0 es0 te0 fe1 ->
                forall s1 : SSAStore.t,
                  well_formed_bexps es1 te1 && Fq2bvq.well_formed_unpackedbf ubf1 te1 ->
                  conformed_bexps es1 s1 te1 && Fq2bvq.conform_unpackedbf ubf1 s1 te1 ->
                  eval_bexps es1 s1 ->
                    forall pack_s1 pack_e1 pack_m1, 
                      (pack_s1, pack_e1, pack_m1) = pack wb_mlen1 wb_elen1 ubf1 ->
                        forall smt_s1 smt_e1 smt_m1 elen1 mlen1,
                          eval_fp_exp fe1 s0 (SMTLIBfp.ieee754_fp smt_s1 smt_e1 smt_m1) elen1 mlen1 ->
          forall g2 te2 es2 ubf2 wb_elen2 wb_mlen2,
              (te2, g2, es2, ubf2, wb_elen2, wb_mlen2) = word_blast_exp gen_var g1 es1 te1 fe2 ->
                forall s2 : SSAStore.t,
                  well_formed_bexps es2 te2 && Fq2bvq.well_formed_unpackedbf ubf2 te2 ->
                  conformed_bexps es2 s2 te2 && Fq2bvq.conform_unpackedbf ubf2 s2 te2 ->
                  eval_bexps es2 s2 ->
                    forall pack_s2 pack_e2 pack_m2, 
                      (pack_s2, pack_e2, pack_m2) = pack wb_mlen2 wb_elen2 ubf2 ->
                        forall smt_s2 smt_e2 smt_m2 elen2 mlen2,
                          eval_fp_exp fe2 s0 (SMTLIBfp.ieee754_fp smt_s2 smt_e2 smt_m2) elen2 mlen2 ->
                            (elen1 = wb_elen1 /\
                            mlen1 = wb_mlen1 /\
                            smt_s1 = (QFBV.eval_exp pack_s1 s1) /\ 
                            smt_e1 = (QFBV.eval_exp pack_e1 s1) /\ 
                            smt_m1 = (QFBV.eval_exp pack_m1 s1)) /\ 
                            (elen2 = wb_elen2 /\
                            mlen2 = wb_mlen2 /\
                            smt_s2 = (QFBV.eval_exp pack_s2 s2) /\ 
                            smt_e2 = (QFBV.eval_exp pack_e2 s2) /\ 
                            smt_m2 = (QFBV.eval_exp pack_m2 s2))) -> 
      forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
        Fq2bvq.well_formed_fp_exp (Fq2bvq.FEbinop op fe1 fe2) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' ubf wb_elen wb_mlen,
              valid_gen_var gen_var ->
                (te', g', es', ubf, wb_elen, wb_mlen) = word_blast_exp gen_var g es te (Fq2bvq.FEbinop op fe1 fe2)->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && Fq2bvq.well_formed_unpackedbf ubf te' ->
                    conformed_bexps es' s' te' && Fq2bvq.conform_unpackedbf ubf s' te' ->
                    eval_bexps es' s' ->
                      forall pack_s pack_e pack_m, 
                        (pack_s, pack_e, pack_m) = pack wb_mlen wb_elen ubf ->
                          (forall smt_s smt_e smt_m elen mlen,
                            eval_fp_exp  (Fq2bvq.FEbinop op fe1 fe2) s (SMTLIBfp.ieee754_fp smt_s smt_e smt_m) elen mlen ->
                            elen = wb_elen /\
                            mlen = wb_mlen /\
                            smt_s = (QFBV.eval_exp pack_s s') /\ 
                            smt_e = (QFBV.eval_exp pack_e s') /\ 
                            smt_m = (QFBV.eval_exp pack_m s')).
Proof.
Admitted.

End EBinop.

Section ERMBinop.

Lemma word_blasting_fp_exp_semantics_equivalence_add :
  forall (rm : QFBV.exp) (fe1 : Fq2bvq.fp_exp) (fe2 : Fq2bvq.fp_exp),
(*     exp_constraint rm -> *)
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_exp fe1 te0 ->
      Fq2bvq.well_formed_fp_exp fe2 te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1,
            valid_gen_var gen_var ->
              (te1, g1, es1, ubf1, wb_elen1, wb_mlen1) = word_blast_exp gen_var g0 es0 te0 fe1 ->
                forall s1 : SSAStore.t,
                  well_formed_bexps es1 te1 && Fq2bvq.well_formed_unpackedbf ubf1 te1 ->
                  conformed_bexps es1 s1 te1 && Fq2bvq.conform_unpackedbf ubf1 s1 te1 ->
                  eval_bexps es1 s1 ->
                    forall pack_s1 pack_e1 pack_m1, 
                      (pack_s1, pack_e1, pack_m1) = pack wb_mlen1 wb_elen1 ubf1 ->
                        forall smt_s1 smt_e1 smt_m1 elen1 mlen1,
                          eval_fp_exp fe1 s0 (SMTLIBfp.ieee754_fp smt_s1 smt_e1 smt_m1) elen1 mlen1 ->
          forall g2 te2 es2 ubf2 wb_elen2 wb_mlen2,
              (te2, g2, es2, ubf2, wb_elen2, wb_mlen2) = word_blast_exp gen_var g1 es1 te1 fe2 ->
                forall s2 : SSAStore.t,
                  well_formed_bexps es2 te2 && Fq2bvq.well_formed_unpackedbf ubf2 te2 ->
                  conformed_bexps es2 s2 te2 && Fq2bvq.conform_unpackedbf ubf2 s2 te2 ->
                  eval_bexps es2 s2 ->
                    forall pack_s2 pack_e2 pack_m2, 
                      (pack_s2, pack_e2, pack_m2) = pack wb_mlen2 wb_elen2 ubf2 ->
                        forall smt_s2 smt_e2 smt_m2 elen2 mlen2,
                          eval_fp_exp fe2 s0 (SMTLIBfp.ieee754_fp smt_s2 smt_e2 smt_m2) elen2 mlen2 ->
                            (elen1 = wb_elen1 /\
                            mlen1 = wb_mlen1 /\
                            smt_s1 = (QFBV.eval_exp pack_s1 s1) /\ 
                            smt_e1 = (QFBV.eval_exp pack_e1 s1) /\ 
                            smt_m1 = (QFBV.eval_exp pack_m1 s1)) /\ 
                            (elen2 = wb_elen2 /\
                            mlen2 = wb_mlen2 /\
                            smt_s2 = (QFBV.eval_exp pack_s2 s2) /\ 
                            smt_e2 = (QFBV.eval_exp pack_e2 s2) /\ 
                            smt_m2 = (QFBV.eval_exp pack_m2 s2))) -> 
      forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
        Fq2bvq.well_formed_fp_exp (Fq2bvq.FErmbinop Fq2bvq.FRBadd rm fe1 fe2) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' ubf wb_elen wb_mlen,
              valid_gen_var gen_var ->
                (te', g', es', ubf, wb_elen, wb_mlen) = word_blast_exp gen_var g es te (Fq2bvq.FErmbinop Fq2bvq.FRBadd rm fe1 fe2)->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && Fq2bvq.well_formed_unpackedbf ubf te' ->
                    conformed_bexps es' s' te' && Fq2bvq.conform_unpackedbf ubf s' te' ->
                    eval_bexps es' s' ->
                      forall pack_s pack_e pack_m, 
                        (pack_s, pack_e, pack_m) = pack wb_mlen wb_elen ubf ->
                          (forall smt_s smt_e smt_m elen mlen,
                            eval_fp_exp (Fq2bvq.FErmbinop Fq2bvq.FRBadd rm fe1 fe2) s (SMTLIBfp.ieee754_fp smt_s smt_e smt_m) elen mlen ->
                            elen = wb_elen /\
                            mlen = wb_mlen /\
                            smt_s = (QFBV.eval_exp pack_s s') /\ 
                            smt_e = (QFBV.eval_exp pack_e s') /\ 
                            smt_m = (QFBV.eval_exp pack_m s')).
Proof.
Admitted.

Lemma word_blasting_fp_exp_semantics_equivalence_sub :
  forall (rm : QFBV.exp) (fe1 : Fq2bvq.fp_exp) (fe2 : Fq2bvq.fp_exp),
(*     exp_constraint rm -> *)
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_exp fe1 te0 ->
      Fq2bvq.well_formed_fp_exp fe2 te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1,
            valid_gen_var gen_var ->
              (te1, g1, es1, ubf1, wb_elen1, wb_mlen1) = word_blast_exp gen_var g0 es0 te0 fe1 ->
                forall s1 : SSAStore.t,
                  well_formed_bexps es1 te1 && Fq2bvq.well_formed_unpackedbf ubf1 te1 ->
                  conformed_bexps es1 s1 te1 && Fq2bvq.conform_unpackedbf ubf1 s1 te1 ->
                  eval_bexps es1 s1 ->
                    forall pack_s1 pack_e1 pack_m1, 
                      (pack_s1, pack_e1, pack_m1) = pack wb_mlen1 wb_elen1 ubf1 ->
                        forall smt_s1 smt_e1 smt_m1 elen1 mlen1,
                          eval_fp_exp fe1 s0 (SMTLIBfp.ieee754_fp smt_s1 smt_e1 smt_m1) elen1 mlen1 ->
          forall g2 te2 es2 ubf2 wb_elen2 wb_mlen2,
              (te2, g2, es2, ubf2, wb_elen2, wb_mlen2) = word_blast_exp gen_var g1 es1 te1 fe2 ->
                forall s2 : SSAStore.t,
                  well_formed_bexps es2 te2 && Fq2bvq.well_formed_unpackedbf ubf2 te2 ->
                  conformed_bexps es2 s2 te2 && Fq2bvq.conform_unpackedbf ubf2 s2 te2 ->
                  eval_bexps es2 s2 ->
                    forall pack_s2 pack_e2 pack_m2, 
                      (pack_s2, pack_e2, pack_m2) = pack wb_mlen2 wb_elen2 ubf2 ->
                        forall smt_s2 smt_e2 smt_m2 elen2 mlen2,
                          eval_fp_exp fe2 s0 (SMTLIBfp.ieee754_fp smt_s2 smt_e2 smt_m2) elen2 mlen2 ->
                            (elen1 = wb_elen1 /\
                            mlen1 = wb_mlen1 /\
                            smt_s1 = (QFBV.eval_exp pack_s1 s1) /\ 
                            smt_e1 = (QFBV.eval_exp pack_e1 s1) /\ 
                            smt_m1 = (QFBV.eval_exp pack_m1 s1)) /\ 
                            (elen2 = wb_elen2 /\
                            mlen2 = wb_mlen2 /\
                            smt_s2 = (QFBV.eval_exp pack_s2 s2) /\ 
                            smt_e2 = (QFBV.eval_exp pack_e2 s2) /\ 
                            smt_m2 = (QFBV.eval_exp pack_m2 s2))) -> 
      forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
        Fq2bvq.well_formed_fp_exp (Fq2bvq.FErmbinop Fq2bvq.FRBsub rm fe1 fe2) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' ubf wb_elen wb_mlen,
              valid_gen_var gen_var ->
                (te', g', es', ubf, wb_elen, wb_mlen) = word_blast_exp gen_var g es te (Fq2bvq.FErmbinop Fq2bvq.FRBsub rm fe1 fe2)->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && Fq2bvq.well_formed_unpackedbf ubf te' ->
                    conformed_bexps es' s' te' && Fq2bvq.conform_unpackedbf ubf s' te' ->
                    eval_bexps es' s' ->
                      forall pack_s pack_e pack_m, 
                        (pack_s, pack_e, pack_m) = pack wb_mlen wb_elen ubf ->
                          (forall smt_s smt_e smt_m elen mlen,
                            eval_fp_exp (Fq2bvq.FErmbinop Fq2bvq.FRBsub rm fe1 fe2) s (SMTLIBfp.ieee754_fp smt_s smt_e smt_m) elen mlen ->
                            elen = wb_elen /\
                            mlen = wb_mlen /\
                            smt_s = (QFBV.eval_exp pack_s s') /\ 
                            smt_e = (QFBV.eval_exp pack_e s') /\ 
                            smt_m = (QFBV.eval_exp pack_m s')).
Proof.
Admitted.

Lemma word_blasting_fp_exp_semantics_equivalence_mul :
  forall (rm : QFBV.exp) (fe1 : Fq2bvq.fp_exp) (fe2 : Fq2bvq.fp_exp),
(*     exp_constraint rm -> *)
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_exp fe1 te0 ->
      Fq2bvq.well_formed_fp_exp fe2 te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1,
            valid_gen_var gen_var ->
              (te1, g1, es1, ubf1, wb_elen1, wb_mlen1) = word_blast_exp gen_var g0 es0 te0 fe1 ->
                forall s1 : SSAStore.t,
                  well_formed_bexps es1 te1 && Fq2bvq.well_formed_unpackedbf ubf1 te1 ->
                  conformed_bexps es1 s1 te1 && Fq2bvq.conform_unpackedbf ubf1 s1 te1 ->
                  eval_bexps es1 s1 ->
                    forall pack_s1 pack_e1 pack_m1, 
                      (pack_s1, pack_e1, pack_m1) = pack wb_mlen1 wb_elen1 ubf1 ->
                        forall smt_s1 smt_e1 smt_m1 elen1 mlen1,
                          eval_fp_exp fe1 s0 (SMTLIBfp.ieee754_fp smt_s1 smt_e1 smt_m1) elen1 mlen1 ->
          forall g2 te2 es2 ubf2 wb_elen2 wb_mlen2,
              (te2, g2, es2, ubf2, wb_elen2, wb_mlen2) = word_blast_exp gen_var g1 es1 te1 fe2 ->
                forall s2 : SSAStore.t,
                  well_formed_bexps es2 te2 && Fq2bvq.well_formed_unpackedbf ubf2 te2 ->
                  conformed_bexps es2 s2 te2 && Fq2bvq.conform_unpackedbf ubf2 s2 te2 ->
                  eval_bexps es2 s2 ->
                    forall pack_s2 pack_e2 pack_m2, 
                      (pack_s2, pack_e2, pack_m2) = pack wb_mlen2 wb_elen2 ubf2 ->
                        forall smt_s2 smt_e2 smt_m2 elen2 mlen2,
                          eval_fp_exp fe2 s0 (SMTLIBfp.ieee754_fp smt_s2 smt_e2 smt_m2) elen2 mlen2 ->
                            (elen1 = wb_elen1 /\
                            mlen1 = wb_mlen1 /\
                            smt_s1 = (QFBV.eval_exp pack_s1 s1) /\ 
                            smt_e1 = (QFBV.eval_exp pack_e1 s1) /\ 
                            smt_m1 = (QFBV.eval_exp pack_m1 s1)) /\ 
                            (elen2 = wb_elen2 /\
                            mlen2 = wb_mlen2 /\
                            smt_s2 = (QFBV.eval_exp pack_s2 s2) /\ 
                            smt_e2 = (QFBV.eval_exp pack_e2 s2) /\ 
                            smt_m2 = (QFBV.eval_exp pack_m2 s2))) -> 
      forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
        Fq2bvq.well_formed_fp_exp (Fq2bvq.FErmbinop Fq2bvq.FRBmul rm fe1 fe2) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' ubf wb_elen wb_mlen,
              valid_gen_var gen_var ->
                (te', g', es', ubf, wb_elen, wb_mlen) = word_blast_exp gen_var g es te (Fq2bvq.FErmbinop Fq2bvq.FRBmul rm fe1 fe2)->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && Fq2bvq.well_formed_unpackedbf ubf te' ->
                    conformed_bexps es' s' te' && Fq2bvq.conform_unpackedbf ubf s' te' ->
                    eval_bexps es' s' ->
                      forall pack_s pack_e pack_m, 
                        (pack_s, pack_e, pack_m) = pack wb_mlen wb_elen ubf ->
                          (forall smt_s smt_e smt_m elen mlen,
                            eval_fp_exp (Fq2bvq.FErmbinop Fq2bvq.FRBmul rm fe1 fe2) s (SMTLIBfp.ieee754_fp smt_s smt_e smt_m) elen mlen ->
                            elen = wb_elen /\
                            mlen = wb_mlen /\
                            smt_s = (QFBV.eval_exp pack_s s') /\ 
                            smt_e = (QFBV.eval_exp pack_e s') /\ 
                            smt_m = (QFBV.eval_exp pack_m s')).
Proof.
Admitted.

Lemma word_blasting_fp_exp_semantics_equivalence_div :
  forall (rm : QFBV.exp) (fe1 : Fq2bvq.fp_exp) (fe2 : Fq2bvq.fp_exp),
(*     exp_constraint rm -> *)
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_exp fe1 te0 ->
      Fq2bvq.well_formed_fp_exp fe2 te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1,
            valid_gen_var gen_var ->
              (te1, g1, es1, ubf1, wb_elen1, wb_mlen1) = word_blast_exp gen_var g0 es0 te0 fe1 ->
                forall s1 : SSAStore.t,
                  well_formed_bexps es1 te1 && Fq2bvq.well_formed_unpackedbf ubf1 te1 ->
                  conformed_bexps es1 s1 te1 && Fq2bvq.conform_unpackedbf ubf1 s1 te1 ->
                  eval_bexps es1 s1 ->
                    forall pack_s1 pack_e1 pack_m1, 
                      (pack_s1, pack_e1, pack_m1) = pack wb_mlen1 wb_elen1 ubf1 ->
                        forall smt_s1 smt_e1 smt_m1 elen1 mlen1,
                          eval_fp_exp fe1 s0 (SMTLIBfp.ieee754_fp smt_s1 smt_e1 smt_m1) elen1 mlen1 ->
          forall g2 te2 es2 ubf2 wb_elen2 wb_mlen2,
              (te2, g2, es2, ubf2, wb_elen2, wb_mlen2) = word_blast_exp gen_var g1 es1 te1 fe2 ->
                forall s2 : SSAStore.t,
                  well_formed_bexps es2 te2 && Fq2bvq.well_formed_unpackedbf ubf2 te2 ->
                  conformed_bexps es2 s2 te2 && Fq2bvq.conform_unpackedbf ubf2 s2 te2 ->
                  eval_bexps es2 s2 ->
                    forall pack_s2 pack_e2 pack_m2, 
                      (pack_s2, pack_e2, pack_m2) = pack wb_mlen2 wb_elen2 ubf2 ->
                        forall smt_s2 smt_e2 smt_m2 elen2 mlen2,
                          eval_fp_exp fe2 s0 (SMTLIBfp.ieee754_fp smt_s2 smt_e2 smt_m2) elen2 mlen2 ->
                            (elen1 = wb_elen1 /\
                            mlen1 = wb_mlen1 /\
                            smt_s1 = (QFBV.eval_exp pack_s1 s1) /\ 
                            smt_e1 = (QFBV.eval_exp pack_e1 s1) /\ 
                            smt_m1 = (QFBV.eval_exp pack_m1 s1)) /\ 
                            (elen2 = wb_elen2 /\
                            mlen2 = wb_mlen2 /\
                            smt_s2 = (QFBV.eval_exp pack_s2 s2) /\ 
                            smt_e2 = (QFBV.eval_exp pack_e2 s2) /\ 
                            smt_m2 = (QFBV.eval_exp pack_m2 s2))) -> 
      forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
        Fq2bvq.well_formed_fp_exp (Fq2bvq.FErmbinop Fq2bvq.FRBdiv rm fe1 fe2) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' ubf wb_elen wb_mlen,
              valid_gen_var gen_var ->
                (te', g', es', ubf, wb_elen, wb_mlen) = word_blast_exp gen_var g es te (Fq2bvq.FErmbinop Fq2bvq.FRBdiv rm fe1 fe2)->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && Fq2bvq.well_formed_unpackedbf ubf te' ->
                    conformed_bexps es' s' te' && Fq2bvq.conform_unpackedbf ubf s' te' ->
                    eval_bexps es' s' ->
                      forall pack_s pack_e pack_m, 
                        (pack_s, pack_e, pack_m) = pack wb_mlen wb_elen ubf ->
                          (forall smt_s smt_e smt_m elen mlen,
                            eval_fp_exp (Fq2bvq.FErmbinop Fq2bvq.FRBdiv rm fe1 fe2) s (SMTLIBfp.ieee754_fp smt_s smt_e smt_m) elen mlen ->
                            elen = wb_elen /\
                            mlen = wb_mlen /\
                            smt_s = (QFBV.eval_exp pack_s s') /\ 
                            smt_e = (QFBV.eval_exp pack_e s') /\ 
                            smt_m = (QFBV.eval_exp pack_m s')).
Proof.
Admitted.

Lemma word_blasting_fp_exp_semantics_equivalence_rmbinop :
  forall (op : Fq2bvq.fermbinop) (rm : QFBV.exp) (fe1 : Fq2bvq.fp_exp) (fe2 : Fq2bvq.fp_exp),
(*     exp_constraint rm -> *)
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_exp fe1 te0 ->
      Fq2bvq.well_formed_fp_exp fe2 te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1,
            valid_gen_var gen_var ->
              (te1, g1, es1, ubf1, wb_elen1, wb_mlen1) = word_blast_exp gen_var g0 es0 te0 fe1 ->
                forall s1 : SSAStore.t,
                  well_formed_bexps es1 te1 && Fq2bvq.well_formed_unpackedbf ubf1 te1 ->
                  conformed_bexps es1 s1 te1 && Fq2bvq.conform_unpackedbf ubf1 s1 te1 ->
                  eval_bexps es1 s1 ->
                    forall pack_s1 pack_e1 pack_m1, 
                      (pack_s1, pack_e1, pack_m1) = pack wb_mlen1 wb_elen1 ubf1 ->
                        forall smt_s1 smt_e1 smt_m1 elen1 mlen1,
                          eval_fp_exp fe1 s0 (SMTLIBfp.ieee754_fp smt_s1 smt_e1 smt_m1) elen1 mlen1 ->
          forall g2 te2 es2 ubf2 wb_elen2 wb_mlen2,
              (te2, g2, es2, ubf2, wb_elen2, wb_mlen2) = word_blast_exp gen_var g1 es1 te1 fe2 ->
                forall s2 : SSAStore.t,
                  well_formed_bexps es2 te2 && Fq2bvq.well_formed_unpackedbf ubf2 te2 ->
                  conformed_bexps es2 s2 te2 && Fq2bvq.conform_unpackedbf ubf2 s2 te2 ->
                  eval_bexps es2 s2 ->
                    forall pack_s2 pack_e2 pack_m2, 
                      (pack_s2, pack_e2, pack_m2) = pack wb_mlen2 wb_elen2 ubf2 ->
                        forall smt_s2 smt_e2 smt_m2 elen2 mlen2,
                          eval_fp_exp fe2 s0 (SMTLIBfp.ieee754_fp smt_s2 smt_e2 smt_m2) elen2 mlen2 ->
                            (elen1 = wb_elen1 /\
                            mlen1 = wb_mlen1 /\
                            smt_s1 = (QFBV.eval_exp pack_s1 s1) /\ 
                            smt_e1 = (QFBV.eval_exp pack_e1 s1) /\ 
                            smt_m1 = (QFBV.eval_exp pack_m1 s1)) /\ 
                            (elen2 = wb_elen2 /\
                            mlen2 = wb_mlen2 /\
                            smt_s2 = (QFBV.eval_exp pack_s2 s2) /\ 
                            smt_e2 = (QFBV.eval_exp pack_e2 s2) /\ 
                            smt_m2 = (QFBV.eval_exp pack_m2 s2))) -> 
      forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
        Fq2bvq.well_formed_fp_exp (Fq2bvq.FErmbinop op rm fe1 fe2) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' ubf wb_elen wb_mlen,
              valid_gen_var gen_var ->
                (te', g', es', ubf, wb_elen, wb_mlen) = word_blast_exp gen_var g es te (Fq2bvq.FErmbinop op rm fe1 fe2) ->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && Fq2bvq.well_formed_unpackedbf ubf te' ->
                    conformed_bexps es' s' te' && Fq2bvq.conform_unpackedbf ubf s' te' ->
                    eval_bexps es' s' ->
                      forall pack_s pack_e pack_m, 
                        (pack_s, pack_e, pack_m) = pack wb_mlen wb_elen ubf ->
                          (forall smt_s smt_e smt_m elen mlen,
                            eval_fp_exp (Fq2bvq.FErmbinop op rm fe1 fe2) s (SMTLIBfp.ieee754_fp smt_s smt_e smt_m) elen mlen ->
                            elen = wb_elen /\
                            mlen = wb_mlen /\
                            smt_s = (QFBV.eval_exp pack_s s') /\ 
                            smt_e = (QFBV.eval_exp pack_e s') /\ 
                            smt_m = (QFBV.eval_exp pack_m s')).
Proof.
Admitted.

End ERMBinop.

Section ERMTriop.

Lemma word_blasting_fp_exp_semantics_equivalence_fma :
  forall (rm : QFBV.exp) (fe1 : Fq2bvq.fp_exp) (fe2 : Fq2bvq.fp_exp) (fe3 : Fq2bvq.fp_exp),
(*     exp_constraint rm -> *)
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_exp fe1 te0 ->
      Fq2bvq.well_formed_fp_exp fe2 te0 ->
      Fq2bvq.well_formed_fp_exp fe3 te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1,
            valid_gen_var gen_var ->
              (te1, g1, es1, ubf1, wb_elen1, wb_mlen1) = word_blast_exp gen_var g0 es0 te0 fe1 ->
                forall s1 : SSAStore.t,
                  well_formed_bexps es1 te1 && Fq2bvq.well_formed_unpackedbf ubf1 te1 ->
                  conformed_bexps es1 s1 te1 && Fq2bvq.conform_unpackedbf ubf1 s1 te1 ->
                  eval_bexps es1 s1 ->
                    forall pack_s1 pack_e1 pack_m1, 
                      (pack_s1, pack_e1, pack_m1) = pack wb_mlen1 wb_elen1 ubf1 ->
                        forall smt_s1 smt_e1 smt_m1 elen1 mlen1,
                          eval_fp_exp fe1 s1 (SMTLIBfp.ieee754_fp smt_s1 smt_e1 smt_m1) elen1 mlen1 ->
          forall g2 te2 es2 ubf2 wb_elen2 wb_mlen2,
              (te2, g2, es2, ubf2, wb_elen2, wb_mlen2) = word_blast_exp gen_var g1 es1 te1 fe2 ->
                forall s2 : SSAStore.t,
                  well_formed_bexps es2 te2 && Fq2bvq.well_formed_unpackedbf ubf2 te2 ->
                  conformed_bexps es2 s2 te2 && Fq2bvq.conform_unpackedbf ubf2 s2 te2 ->
                  eval_bexps es2 s2 ->
                    forall pack_s2 pack_e2 pack_m2, 
                      (pack_s2, pack_e2, pack_m2) = pack wb_mlen2 wb_elen2 ubf2 ->
                        forall smt_s2 smt_e2 smt_m2 elen2 mlen2,
                          eval_fp_exp fe2 s2 (SMTLIBfp.ieee754_fp smt_s2 smt_e2 smt_m2) elen2 mlen2 ->
          forall g3 te3 es3 ubf3 wb_elen3 wb_mlen3,
              (te3, g3, es3, ubf3, wb_elen3, wb_mlen3) = word_blast_exp gen_var g2 es2 te2 fe3 ->
                forall s3 : SSAStore.t,
                  well_formed_bexps es3 te3 && Fq2bvq.well_formed_unpackedbf ubf3 te3 ->
                  conformed_bexps es3 s3 te3 && Fq2bvq.conform_unpackedbf ubf3 s3 te3 ->
                  eval_bexps es3 s3 ->
                    forall pack_s3 pack_e3 pack_m3, 
                      (pack_s3, pack_e3, pack_m3) = pack wb_mlen3 wb_elen3 ubf3 ->
                        forall smt_s3 smt_e3 smt_m3 elen3 mlen3,
                          eval_fp_exp fe3 s3 (SMTLIBfp.ieee754_fp smt_s3 smt_e3 smt_m3) elen3 mlen3 ->
                            (elen1 = wb_elen1 /\
                            mlen1 = wb_mlen1 /\
                            smt_s1 = (QFBV.eval_exp pack_s1 s1) /\ 
                            smt_e1 = (QFBV.eval_exp pack_e1 s1) /\ 
                            smt_m1 = (QFBV.eval_exp pack_m1 s1)) /\ 
                            (elen2 = wb_elen2 /\
                            mlen2 = wb_mlen2 /\
                            smt_s2 = (QFBV.eval_exp pack_s2 s2) /\ 
                            smt_e2 = (QFBV.eval_exp pack_e2 s2) /\ 
                            smt_m2 = (QFBV.eval_exp pack_m2 s2)) /\
                            (elen3 = wb_elen3 /\
                            mlen3 = wb_mlen3 /\
                            smt_s3 = (QFBV.eval_exp pack_s3 s3) /\ 
                            smt_e3 = (QFBV.eval_exp pack_e3 s3) /\ 
                            smt_m3 = (QFBV.eval_exp pack_m3 s3))) ->  
      forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
        Fq2bvq.well_formed_fp_exp (Fq2bvq.FErmtriop Fq2bvq.FRTfma rm fe1 fe2 fe3) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' ubf wb_elen wb_mlen,
              valid_gen_var gen_var ->
                (te', g', es', ubf, wb_elen, wb_mlen) = word_blast_exp gen_var g es te (Fq2bvq.FErmtriop Fq2bvq.FRTfma rm fe1 fe2 fe3) ->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && Fq2bvq.well_formed_unpackedbf ubf te' ->
                    conformed_bexps es' s' te' && Fq2bvq.conform_unpackedbf ubf s' te' ->
                    eval_bexps es' s' ->
                      forall pack_s pack_e pack_m, 
                        (pack_s, pack_e, pack_m) = pack wb_mlen wb_elen ubf ->
                          (forall smt_s smt_e smt_m elen mlen,
                            eval_fp_exp (Fq2bvq.FErmtriop Fq2bvq.FRTfma rm fe1 fe2 fe3) s' (SMTLIBfp.ieee754_fp smt_s smt_e smt_m) elen mlen ->
                            elen = wb_elen /\
                            mlen = wb_mlen /\
                            smt_s = (QFBV.eval_exp pack_s s') /\ 
                            smt_e = (QFBV.eval_exp pack_e s') /\ 
                            smt_m = (QFBV.eval_exp pack_m s')).
Proof.
Admitted.

Lemma word_blasting_fp_exp_semantics_equivalence_rmtriop :
  forall (op : Fq2bvq.fermtriop) (rm : QFBV.exp) (fe1 : Fq2bvq.fp_exp) (fe2 : Fq2bvq.fp_exp) (fe3 : Fq2bvq.fp_exp),
(*     exp_constraint rm -> *)
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_exp fe1 te0 ->
      Fq2bvq.well_formed_fp_exp fe2 te0 ->
      Fq2bvq.well_formed_fp_exp fe3 te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1,
            valid_gen_var gen_var ->
              (te1, g1, es1, ubf1, wb_elen1, wb_mlen1) = word_blast_exp gen_var g0 es0 te0 fe1 ->
                forall s1 : SSAStore.t,
                  well_formed_bexps es1 te1 && Fq2bvq.well_formed_unpackedbf ubf1 te1 ->
                  conformed_bexps es1 s1 te1 && Fq2bvq.conform_unpackedbf ubf1 s1 te1 ->
                  eval_bexps es1 s1 ->
                    forall pack_s1 pack_e1 pack_m1, 
                      (pack_s1, pack_e1, pack_m1) = pack wb_mlen1 wb_elen1 ubf1 ->
                        forall smt_s1 smt_e1 smt_m1 elen1 mlen1,
                          eval_fp_exp fe1 s0 (SMTLIBfp.ieee754_fp smt_s1 smt_e1 smt_m1) elen1 mlen1 ->
          forall g2 te2 es2 ubf2 wb_elen2 wb_mlen2,
              (te2, g2, es2, ubf2, wb_elen2, wb_mlen2) = word_blast_exp gen_var g1 es1 te1 fe2 ->
                forall s2 : SSAStore.t,
                  well_formed_bexps es2 te2 && Fq2bvq.well_formed_unpackedbf ubf2 te2 ->
                  conformed_bexps es2 s2 te2 && Fq2bvq.conform_unpackedbf ubf2 s2 te2 ->
                  eval_bexps es2 s2 ->
                    forall pack_s2 pack_e2 pack_m2, 
                      (pack_s2, pack_e2, pack_m2) = pack wb_mlen2 wb_elen2 ubf2 ->
                        forall smt_s2 smt_e2 smt_m2 elen2 mlen2,
                          eval_fp_exp fe2 s0 (SMTLIBfp.ieee754_fp smt_s2 smt_e2 smt_m2) elen2 mlen2 ->
          forall g3 te3 es3 ubf3 wb_elen3 wb_mlen3,
              (te3, g3, es3, ubf3, wb_elen3, wb_mlen3) = word_blast_exp gen_var g2 es2 te2 fe3 ->
                forall s3 : SSAStore.t,
                  well_formed_bexps es3 te3 && Fq2bvq.well_formed_unpackedbf ubf3 te3 ->
                  conformed_bexps es3 s3 te3 && Fq2bvq.conform_unpackedbf ubf3 s3 te3 ->
                  eval_bexps es3 s3 ->
                    forall pack_s3 pack_e3 pack_m3, 
                      (pack_s3, pack_e3, pack_m3) = pack wb_mlen3 wb_elen3 ubf3 ->
                        forall smt_s3 smt_e3 smt_m3 elen3 mlen3,
                          eval_fp_exp fe3 s0 (SMTLIBfp.ieee754_fp smt_s3 smt_e3 smt_m3) elen3 mlen3 ->
                            (elen1 = wb_elen1 /\
                            mlen1 = wb_mlen1 /\
                            smt_s1 = (QFBV.eval_exp pack_s1 s1) /\ 
                            smt_e1 = (QFBV.eval_exp pack_e1 s1) /\ 
                            smt_m1 = (QFBV.eval_exp pack_m1 s1)) /\ 
                            (elen2 = wb_elen2 /\
                            mlen2 = wb_mlen2 /\
                            smt_s2 = (QFBV.eval_exp pack_s2 s2) /\ 
                            smt_e2 = (QFBV.eval_exp pack_e2 s2) /\ 
                            smt_m2 = (QFBV.eval_exp pack_m2 s2)) /\
                            (elen3 = wb_elen3 /\
                            mlen3 = wb_mlen3 /\
                            smt_s3 = (QFBV.eval_exp pack_s3 s3) /\ 
                            smt_e3 = (QFBV.eval_exp pack_e3 s3) /\ 
                            smt_m3 = (QFBV.eval_exp pack_m3 s3))) ->  
      forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
        Fq2bvq.well_formed_fp_exp (Fq2bvq.FErmtriop op rm fe1 fe2 fe3) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' ubf wb_elen wb_mlen,
              valid_gen_var gen_var ->
                (te', g', es', ubf, wb_elen, wb_mlen) = word_blast_exp gen_var g es te (Fq2bvq.FErmtriop op rm fe1 fe2 fe3) ->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && Fq2bvq.well_formed_unpackedbf ubf te' ->
                    conformed_bexps es' s' te' && Fq2bvq.conform_unpackedbf ubf s' te' ->
                    eval_bexps es' s' ->
                      forall pack_s pack_e pack_m, 
                        (pack_s, pack_e, pack_m) = pack wb_mlen wb_elen ubf ->
                          (forall smt_s smt_e smt_m elen mlen,
                            eval_fp_exp (Fq2bvq.FErmtriop op rm fe1 fe2 fe3) s (SMTLIBfp.ieee754_fp smt_s smt_e smt_m) elen mlen ->
                            elen = wb_elen /\
                            mlen = wb_mlen /\
                            smt_s = (QFBV.eval_exp pack_s s') /\ 
                            smt_e = (QFBV.eval_exp pack_e s') /\ 
                            smt_m = (QFBV.eval_exp pack_m s')).
Proof.
Admitted.

End ERMTriop.

Section EConvert.

Lemma word_blasting_fp_exp_semantics_equivalence_ofbf :
  forall (rm : QFBV.exp) (fe : Fq2bvq.fp_exp) (telen tmlen : nat),
(*     exp_constraint rm -> *)
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_exp fe te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1,
            valid_gen_var gen_var ->
              (te1, g1, es1, ubf1, wb_elen1, wb_mlen1) = word_blast_exp gen_var g0 es0 te0 fe ->
                  forall s1 : SSAStore.t,
                    well_formed_bexps es1 te1 && Fq2bvq.well_formed_unpackedbf ubf1 te1 ->
                    conformed_bexps es1 s1 te1 && Fq2bvq.conform_unpackedbf ubf1 s1 te1 ->
                    eval_bexps es1 s1 ->
                      forall pack_s1 pack_e1 pack_m1, 
                        (pack_s1, pack_e1, pack_m1) = pack wb_mlen1 wb_elen1 ubf1 ->
                          forall smt_s1 smt_e1 smt_m1 elen1 mlen1,
                            eval_fp_exp fe s0 (SMTLIBfp.ieee754_fp smt_s1 smt_e1 smt_m1) elen1 mlen1 ->
                            elen1 = wb_elen1 /\
                            mlen1 = wb_mlen1 /\
                            smt_s1 = (QFBV.eval_exp pack_s1 s1) /\ 
                            smt_e1 = (QFBV.eval_exp pack_e1 s1) /\ 
                            smt_m1 = (QFBV.eval_exp pack_m1 s1)) -> 
      forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
        Fq2bvq.well_formed_fp_exp (Fq2bvq.FEofbf rm fe telen tmlen) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' ubf wb_elen wb_mlen,
              valid_gen_var gen_var ->
                (te', g', es', ubf, wb_elen, wb_mlen) = word_blast_exp gen_var g es te (Fq2bvq.FEofbf rm fe telen tmlen)->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && Fq2bvq.well_formed_unpackedbf ubf te' ->
                    conformed_bexps es' s' te' && Fq2bvq.conform_unpackedbf ubf s' te' ->
                    eval_bexps es' s' ->
                      forall pack_s pack_e pack_m, 
                        (pack_s, pack_e, pack_m) = pack wb_mlen wb_elen ubf ->
                          (forall smt_s smt_e smt_m elen mlen,
                            eval_fp_exp (Fq2bvq.FEofbf rm fe telen tmlen) s (SMTLIBfp.ieee754_fp smt_s smt_e smt_m) elen mlen ->
                            elen = wb_elen /\
                            mlen = wb_mlen /\
                            smt_s = (QFBV.eval_exp pack_s s') /\ 
                            smt_e = (QFBV.eval_exp pack_e s') /\ 
                            smt_m = (QFBV.eval_exp pack_m s')).
Proof.
Admitted.

Lemma word_blasting_fp_exp_semantics_equivalence_ofbv :
  forall (e : QFBV.exp) (n telen tmlen : nat),
(*     exp_constraint e -> *)
    forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
      Fq2bvq.well_formed_fp_exp (Fq2bvq.FEofbv e n telen tmlen) te ->
        well_formed_bexps es te ->
        conformed_bexps es s te ->
        eval_bexps es s ->
          forall gen_var g' te' es' ubf wb_elen wb_mlen,
            valid_gen_var gen_var ->
              (te', g', es', ubf, wb_elen, wb_mlen) = word_blast_exp gen_var g es te (Fq2bvq.FEofbv e n telen tmlen)->
                forall s' : SSAStore.t,
                  well_formed_bexps es' te' && Fq2bvq.well_formed_unpackedbf ubf te' ->
                  conformed_bexps es' s' te' && Fq2bvq.conform_unpackedbf ubf s' te' ->
                  eval_bexps es' s' ->
                    forall pack_s pack_e pack_m, 
                      (pack_s, pack_e, pack_m) = pack wb_mlen wb_elen ubf ->
                        forall smt_s smt_e smt_m elen mlen,
                          eval_fp_exp (Fq2bvq.FEofbv e n telen tmlen) s (SMTLIBfp.ieee754_fp smt_s smt_e smt_m) elen mlen ->
                          elen = wb_elen /\
                          mlen = wb_mlen /\
                          smt_s = (QFBV.eval_exp pack_s s') /\ 
                          smt_e = (QFBV.eval_exp pack_e s') /\ 
                          smt_m = (QFBV.eval_exp pack_m s').
Proof.
  move => e n telen tmlen te s es g Hwf Heswf Hescf Hes gen_var g' te' es' ubf wb_elen wb_mlen Hgv wb s' Hwbwf Hwbcf Hes' pack_s pack_e pack_m Hpack smt_s smt_e smt_m elen mlen Hsmt.
  simpl in wb. inversion wb.
  inversion Hsmt. split. reflexivity. split. reflexivity.
Admitted.

Lemma word_blasting_fp_exp_semantics_equivalence_ofsbv :
  forall (rm e : QFBV.exp) (n telen tmlen : nat),
(*     exp_constraint rm && exp_constraint e -> *)
   forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
      Fq2bvq.well_formed_fp_exp (Fq2bvq.FEofsbv rm e n telen tmlen) te ->
        well_formed_bexps es te ->
        conformed_bexps es s te ->
        eval_bexps es s ->
          forall gen_var g' te' es' ubf wb_elen wb_mlen,
            valid_gen_var gen_var ->
              (te', g', es', ubf, wb_elen, wb_mlen) = word_blast_exp gen_var g es te (Fq2bvq.FEofsbv rm e n telen tmlen) ->
                forall s' : SSAStore.t,
                  well_formed_bexps es' te' && Fq2bvq.well_formed_unpackedbf ubf te' ->
                  conformed_bexps es' s' te' && Fq2bvq.conform_unpackedbf ubf s' te' ->
                  eval_bexps es' s' ->
                    forall pack_s pack_e pack_m, 
                      (pack_s, pack_e, pack_m) = pack wb_mlen wb_elen ubf ->
                        (forall smt_s smt_e smt_m elen mlen,
                          eval_fp_exp (Fq2bvq.FEofsbv rm e n telen tmlen) s (SMTLIBfp.ieee754_fp smt_s smt_e smt_m) elen mlen ->
                          elen = wb_elen /\
                          mlen = wb_mlen /\
                          smt_s = (QFBV.eval_exp pack_s s') /\ 
                          smt_e = (QFBV.eval_exp pack_e s') /\ 
                          smt_m = (QFBV.eval_exp pack_m s')).
Proof.
Admitted.

Lemma word_blasting_fp_exp_semantics_equivalence_ofubv :
  forall (rm e : QFBV.exp) (n telen tmlen : nat),
(*     exp_constraint rm && exp_constraint e -> *)
   forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
      Fq2bvq.well_formed_fp_exp (Fq2bvq.FEofubv rm e n telen tmlen) te ->
        well_formed_bexps es te ->
        conformed_bexps es s te ->
        eval_bexps es s ->
          forall gen_var g' te' es' ubf wb_elen wb_mlen,
            valid_gen_var gen_var ->
              (te', g', es', ubf, wb_elen, wb_mlen) = word_blast_exp gen_var g es te (Fq2bvq.FEofubv rm e n telen tmlen) ->
                forall s' : SSAStore.t,
                  well_formed_bexps es' te' && Fq2bvq.well_formed_unpackedbf ubf te' ->
                  conformed_bexps es' s' te' && Fq2bvq.conform_unpackedbf ubf s' te' ->
                  eval_bexps es' s' ->
                    forall pack_s pack_e pack_m, 
                      (pack_s, pack_e, pack_m) = pack wb_mlen wb_elen ubf ->
                        (forall smt_s smt_e smt_m elen mlen,
                          eval_fp_exp (Fq2bvq.FEofubv rm e n telen tmlen) s (SMTLIBfp.ieee754_fp smt_s smt_e smt_m) elen mlen ->
                          elen = wb_elen /\
                          mlen = wb_mlen /\
                          smt_s = (QFBV.eval_exp pack_s s') /\ 
                          smt_e = (QFBV.eval_exp pack_e s') /\ 
                          smt_m = (QFBV.eval_exp pack_m s')).
Proof.
Admitted.

End EConvert.

Lemma word_blasting_fp_exp_semantics_equivalence_ite :
  forall (fb1 : Fq2bvq.fp_bexp) (fe2 : Fq2bvq.fp_exp) (fe3 : Fq2bvq.fp_exp),
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_bexp fb1 te0 ->
      Fq2bvq.well_formed_fp_exp fe2 te0 ->
      Fq2bvq.well_formed_fp_exp fe3 te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 b1,
            valid_gen_var gen_var ->
              (te1, g1, es1, b1) = word_blast_bexp gen_var g0 es0 te0 fb1 ->
                forall s1 : SSAStore.t,
                  well_formed_bexps es1 te1 && QFBV.well_formed_bexp b1 te1 ->
                  conformed_bexps es1 s1 te1 && conform_bexp b1 s1 te1 ->
                  eval_bexps es1 s1 ->
                    forall smt_b1, eval_fp_bexp fb1 s0 smt_b1 ->
          forall g2 te2 es2 ubf2 wb_elen2 wb_mlen2,
              (te2, g2, es2, ubf2, wb_elen2, wb_mlen2) = word_blast_exp gen_var g1 es1 te1 fe2 ->
                forall s2 : SSAStore.t,
                  well_formed_bexps es2 te2 && Fq2bvq.well_formed_unpackedbf ubf2 te2 ->
                  conformed_bexps es2 s2 te2 && Fq2bvq.conform_unpackedbf ubf2 s2 te2 ->
                  eval_bexps es2 s2 ->
                    forall pack_s2 pack_e2 pack_m2, 
                      (pack_s2, pack_e2, pack_m2) = pack wb_mlen2 wb_elen2 ubf2 ->
                        forall smt_s2 smt_e2 smt_m2 elen2 mlen2,
                          eval_fp_exp fe2 s0 (SMTLIBfp.ieee754_fp smt_s2 smt_e2 smt_m2) elen2 mlen2 ->
          forall g3 te3 es3 ubf3 wb_elen3 wb_mlen3,
              (te3, g3, es3, ubf3, wb_elen3, wb_mlen3) = word_blast_exp gen_var g2 es2 te2 fe3 ->
                forall s3 : SSAStore.t,
                  well_formed_bexps es3 te3 && Fq2bvq.well_formed_unpackedbf ubf3 te3 ->
                  conformed_bexps es3 s3 te3 && Fq2bvq.conform_unpackedbf ubf3 s3 te3 ->
                  eval_bexps es3 s3 ->
                    forall pack_s3 pack_e3 pack_m3, 
                      (pack_s3, pack_e3, pack_m3) = pack wb_mlen3 wb_elen3 ubf3 ->
                        forall smt_s3 smt_e3 smt_m3 elen3 mlen3,
                          eval_fp_exp fe3 s0 (SMTLIBfp.ieee754_fp smt_s3 smt_e3 smt_m3) elen3 mlen3 ->
                            (smt_b1 = (QFBV.eval_bexp b1 s1)) /\
                            (elen2 = wb_elen2 /\
                            mlen2 = wb_mlen2 /\
                            smt_s2 = (QFBV.eval_exp pack_s2 s2) /\ 
                            smt_e2 = (QFBV.eval_exp pack_e2 s2) /\ 
                            smt_m2 = (QFBV.eval_exp pack_m2 s2)) /\
                            (elen3 = wb_elen3 /\
                            mlen3 = wb_mlen3 /\
                            smt_s3 = (QFBV.eval_exp pack_s3 s3) /\ 
                            smt_e3 = (QFBV.eval_exp pack_e3 s3) /\ 
                            smt_m3 = (QFBV.eval_exp pack_m3 s3))) -> 
      forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
        Fq2bvq.well_formed_fp_exp (Fq2bvq.FEite fb1 fe2 fe3) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' ubf wb_elen wb_mlen,
              valid_gen_var gen_var ->
                (te', g', es', ubf, wb_elen, wb_mlen) = word_blast_exp gen_var g es te (Fq2bvq.FEite fb1 fe2 fe3)->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && Fq2bvq.well_formed_unpackedbf ubf te' ->
                    conformed_bexps es' s' te' && Fq2bvq.conform_unpackedbf ubf s' te' ->
                    eval_bexps es' s' ->
                      forall pack_s pack_e pack_m, 
                        (pack_s, pack_e, pack_m) = pack wb_mlen wb_elen ubf ->
                          (forall smt_s smt_e smt_m elen mlen,
                            eval_fp_exp (Fq2bvq.FEite fb1 fe2 fe3) s (SMTLIBfp.ieee754_fp smt_s smt_e smt_m) elen mlen ->
                            elen = wb_elen /\
                            mlen = wb_mlen /\
                            smt_s = (QFBV.eval_exp pack_s s') /\ 
                            smt_e = (QFBV.eval_exp pack_e s') /\ 
                            smt_m = (QFBV.eval_exp pack_m s')).
Proof.
  move => fb1 fe2 fe3 IH /= te s es g Hwf Heswf Hescf Hes gen_var g' te' es' ubf wb_elen wb_mlen Hgv wb s' Hwbwf Hwbcf Hes' smt_b Hsmt.
  case Hwb1: (word_blast_bexp gen_var g es te fb1) => [[[te1 g1] es1] b1].
  case Hwb2: (word_blast_exp gen_var g1 es1 te1 fe2) => [[[[[te2 g2] es2] ubf2] wb_elen2] wb_mlen2].
  case Hwb3: (word_blast_exp gen_var g2 es2 te2 fe3) => [[[[[te3 g3] es3] ubf3] wb_elen3] wb_mlen3].
  rewrite Hwb1 Hwb2 Hwb3 in wb. inversion wb. 
Admitted.

Lemma word_blasting_fp_bexp_semantics_equivalence_false :
  forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
    Fq2bvq.well_formed_fp_bexp (Fq2bvq.FBfalse) te ->
        well_formed_bexps es te ->
        conformed_bexps es s te ->
        eval_bexps es s ->
          forall gen_var g' te' es' b,
            valid_gen_var gen_var ->
              (te', g', es', b) = word_blast_bexp gen_var g es te (Fq2bvq.FBfalse) ->
                forall s' : SSAStore.t,
                  well_formed_bexps es' te' && QFBV.well_formed_bexp b te' ->
                  conformed_bexps es' s' te' && conform_bexp b s' te' ->
                  eval_bexps es' s' ->
                    forall smt_b, eval_fp_bexp (Fq2bvq.FBfalse) s smt_b ->
                      smt_b = QFBV.eval_bexp b s'.
Proof.
  move => /= te s es g Hwf Heswf Hescf Hes gen_var g' te' es' b Hgv wb s' Hwbwf Hwbcf Hes' smt_b Hsmt.
  inversion wb. simpl. inversion Hsmt. reflexivity.
Qed.

Lemma word_blasting_fp_bexp_semantics_equivalence_true :
  forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
    Fq2bvq.well_formed_fp_bexp (Fq2bvq.FBfalse) te ->
        well_formed_bexps es te ->
        conformed_bexps es s te ->
        eval_bexps es s ->
          forall gen_var g' te' es' b,
            valid_gen_var gen_var ->
              (te', g', es', b) = word_blast_bexp gen_var g es te (Fq2bvq.FBtrue) ->
                forall s' : SSAStore.t,
                  well_formed_bexps es' te' && QFBV.well_formed_bexp b te' ->
                  conformed_bexps es' s' te' && conform_bexp b s' te' ->
                  eval_bexps es' s' ->
                    forall smt_b, eval_fp_bexp (Fq2bvq.FBtrue) s smt_b ->
                      smt_b = QFBV.eval_bexp b s'.
Proof.
  move => /= te s es g Hwf Heswf Hescf Hes gen_var g' te' es' b Hgv wb s' Hwbwf Hwbcf Hes' smt_b Hsmt.
  inversion wb. simpl. inversion Hsmt. reflexivity.
Qed.

Lemma word_blasting_fp_bexp_semantics_equivalence_boolvar :
  forall e : QFBV.exp,
    forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
      Fq2bvq.well_formed_fp_bexp (Fq2bvq.FBvar e) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' b,
              valid_gen_var gen_var ->
                (te', g', es', b) = word_blast_bexp gen_var g es te (Fq2bvq.FBvar e) ->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && QFBV.well_formed_bexp b te' ->
                    conformed_bexps es' s' te' && conform_bexp b s' te' ->
                    eval_bexps es' s' ->
                      forall smt_b, eval_fp_bexp (Fq2bvq.FBvar e) s smt_b ->
                        smt_b = QFBV.eval_bexp b s'.
Proof.
  move => e /= te s es g Hwf Heswf Hescf Hes gen_var g' te' es' b Hgv wb s' Hwbwf Hwbcf Hes' smt_b Hsmt.
  inversion wb.
  assert (Hb : QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq e (QFBV.Econst [:: true])) s' = QFBV.eval_bexp (QFBV.Bbinop QFBV.Beq e (QFBV.Econst [:: true])) s). admit.
  inversion Hsmt. rewrite Hb H4 //. 
Admitted.

Lemma word_blasting_fp_bexp_semantics_equivalence_bveq :
  forall fe1 fe2: Fq2bvq.fp_exp,
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_exp fe1 te0 ->
      Fq2bvq.well_formed_fp_exp fe2 te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1,
            valid_gen_var gen_var ->
              (te1, g1, es1, ubf1, wb_elen1, wb_mlen1) = word_blast_exp gen_var g0 es0 te0 fe1 ->
                forall s1 : SSAStore.t,
                  well_formed_bexps es1 te1 && Fq2bvq.well_formed_unpackedbf ubf1 te1 ->
                  conformed_bexps es1 s1 te1 && Fq2bvq.conform_unpackedbf ubf1 s1 te1 ->
                  eval_bexps es1 s1 ->
                    forall pack_s1 pack_e1 pack_m1, 
                      (pack_s1, pack_e1, pack_m1) = pack wb_mlen1 wb_elen1 ubf1 ->
                        forall smt_s1 smt_e1 smt_m1 elen1 mlen1,
                          eval_fp_exp fe1 s0 (SMTLIBfp.ieee754_fp smt_s1 smt_e1 smt_m1) elen1 mlen1 ->
          forall g2 te2 es2 ubf2 wb_elen2 wb_mlen2,
              (te2, g2, es2, ubf2, wb_elen2, wb_mlen2) = word_blast_exp gen_var g1 es1 te1 fe2 ->
                forall s2 : SSAStore.t,
                  well_formed_bexps es2 te2 && Fq2bvq.well_formed_unpackedbf ubf2 te2 ->
                  conformed_bexps es2 s2 te2 && Fq2bvq.conform_unpackedbf ubf2 s2 te2 ->
                  eval_bexps es2 s2 ->
                    forall pack_s2 pack_e2 pack_m2, 
                      (pack_s2, pack_e2, pack_m2) = pack wb_mlen2 wb_elen2 ubf2 ->
                        forall smt_s2 smt_e2 smt_m2 elen2 mlen2,
                          eval_fp_exp fe2 s0 (SMTLIBfp.ieee754_fp smt_s2 smt_e2 smt_m2) elen2 mlen2 ->
                            (elen1 = wb_elen1 /\
                            mlen1 = wb_mlen1 /\
                            smt_s1 = (QFBV.eval_exp pack_s1 s1) /\ 
                            smt_e1 = (QFBV.eval_exp pack_e1 s1) /\ 
                            smt_m1 = (QFBV.eval_exp pack_m1 s1)) /\ 
                            (elen2 = wb_elen2 /\
                            mlen2 = wb_mlen2 /\
                            smt_s2 = (QFBV.eval_exp pack_s2 s2) /\ 
                            smt_e2 = (QFBV.eval_exp pack_e2 s2) /\ 
                            smt_m2 = (QFBV.eval_exp pack_m2 s2))) -> 
    forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
      Fq2bvq.well_formed_fp_bexp (Fq2bvq.FBbveq fe1 fe2) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' b,
              valid_gen_var gen_var ->
                (te', g', es', b) = word_blast_bexp gen_var g es te (Fq2bvq.FBbveq fe1 fe2) ->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && QFBV.well_formed_bexp b te' ->
                    conformed_bexps es' s' te' && conform_bexp b s' te' ->
                    eval_bexps es' s' ->
                      forall smt_b, eval_fp_bexp (Fq2bvq.FBbveq fe1 fe2) s smt_b ->
                        smt_b = QFBV.eval_bexp b s'.
Proof.
(*   move => fe1 fe2 IH1 IH2 te Hwf gen_var g g' te' es b Hgv wb Hwbwf s Hwbcf smt_b Hsmt Hes.
  inversion wb. simpl in wb.
  case Hwb1: (word_blast_exp gen_var g [::] te fe1) => [[[[[te1 g1] es1] ubf1] wb_elen1] wb_mlen1].
  case Hwb2: (word_blast_exp gen_var g1 es1 te1 fe2) => [[[[[te2 g2] es2] ubf2] wb_elen2] wb_mlen2].
  rewrite Hwb1 Hwb2 in wb. inversion wb. 
  inversion Hsmt. subst. 
  inversion H10. 
  {
    admit.
  }
  {
    admit.
  } *)
Admitted.

Section BUnop.

Lemma uelen_ge_elen : forall elen mlen, elen > 1 -> mlen > 1 -> unpack_elen mlen elen >= elen.
Proof.
  move => elen mlen Helen Hmlen. 
  unfold unpack_elen. unfold unpack_elen_Z. 
  rewrite Z2Nat.inj_add. simpl. 
  unfold min_subnormal_e. unfold max_subnormal_e. unfold bias. unfold unpack_mlen_Z. unfold unpack_mlen.
  rewrite Nat2Z.inj_add Pos2Nat.inj_1 Nat.add_comm -Nats.addn_add -leq_subLR.
  replace (- (2 ^ (elen_Z elen - 1) - 1) - (Z.of_nat mlen + 1 - 2))%Z with 
    ((Z.opp (2 ^ (elen_Z elen - 1)) - ((Z.of_nat mlen) - 2)))%Z.
  unfold elen_Z.
  rewrite -Z.add_opp_l -Z.opp_add_distr Z.abs_opp. rewrite Z.abs_eq.
  rewrite -(Nat2Z.id (elen - 1)).
  rewrite -(Z.log2_up_pow2 (Z.of_nat (elen - 1))).
  apply Nats.le_leq. apply Z2Nat.inj_le. apply Z.log2_up_nonneg. apply Z.log2_up_nonneg.  
  rewrite Z.add_sub_swap -Z.add_assoc Zplus_minus.
  apply Z.log2_up_le_mono. 
  rewrite -Z.le_sub_le_add_r Nat2Z.inj_sub /=. rewrite Z.sub_diag .  
  apply Zle_minus_le_0. apply Zlt_succ_le. rewrite Z.two_succ. apply Zsucc_lt_compat.
  replace 1%Z with (Z.of_nat 1) by auto.
  apply inj_lt. apply Nats.ltn_lt in Hmlen. exact Hmlen.
  - apply Nats.ltn_lt in Helen. apply Nat.lt_le_incl. exact Helen.
  - lia. 
  - rewrite Z.add_sub_swap -Z.add_assoc Zplus_minus. 
    assert (Hmlen' : (0 <= Z.of_nat mlen - 2)%Z).
    apply Zle_minus_le_0. apply Zlt_succ_le. rewrite Z.two_succ. apply Zsucc_lt_compat. 
    replace 1%Z with (Z.of_nat 1) by auto.
    apply inj_lt. apply Nats.ltn_lt in Hmlen. exact Hmlen.
    apply Z.add_nonneg_nonneg. exact Hmlen'.
    replace 1%Z with (Z.of_nat 1) by auto.
    rewrite -Nat2Z.inj_sub. rewrite -Nats.subn_sub.
    move : (pow2_nat2z_gt0 (elen - 1)). move => Helen'.
     apply Z.lt_le_incl in Helen'. exact Helen'.
  - apply Nats.ltn_lt in Helen. apply Nat.lt_le_incl in Helen. exact Helen.
  - rewrite Z.opp_sub_distr Z.sub_sub_distr Z.sub_add_distr Z.sub_add_distr. lia. 
  - apply Z.log2_up_nonneg. 
  - lia.
Qed.

Lemma elen_can_represent_bias : forall elen mlen, elen > 1 -> mlen > 1 ->
                                (bias elen >= - 2 ^ Z.of_nat elen)%Z /\
                                (bias elen < 2 ^ Z.of_nat elen)%Z. 
Proof.
  intros elen mlen Helen Hmlen. split.
  - unfold bias. unfold elen_Z. apply Z.le_ge.
    apply (Z.le_trans (- 2 ^ Z.of_nat elen)%Z 0%Z (2 ^ (Z.of_nat elen - 1) - 1)%Z).
    * move : (ZAriths.two_power_of_nat_gt0 elen) => Hleft.
      apply Z.gt_lt in Hleft. apply Z.opp_neg_pos in Hleft. 
      apply Z.lt_le_incl. exact Hleft. 
    * rewrite Z.sub_1_r. apply Zgt_0_le_0_pred. 
      replace 1%Z with (Z.of_nat 1)%Z by auto.
      rewrite -Nat2Z.inj_sub.
      apply (ZAriths.two_power_of_nat_gt0 (elen-1)). 
      apply Nats.leq_le. auto.
  - unfold bias. unfold elen_Z.
    replace 1%Z with (Z.of_nat 1)%Z by auto.
    rewrite -Nat2Z.inj_sub. rewrite -Nats.subn_sub. 
    replace (Z.of_nat 1)%Z with 1%Z by auto.
    rewrite Z.sub_1_r. apply Z.lt_pred_le.
    assert (goal' : (2 ^ Z.of_nat (elen - 1) < 2 ^ Z.of_nat elen)%Z).
    {
      apply (Z.pow_lt_mono_r 2%Z (Z.of_nat (elen - 1)) (Z.of_nat elen)).
      lia. replace 0%Z with (Z.of_nat 0) by auto. rewrite -Nat2Z.inj_le. 
      apply Nats.leq_le. auto.
      rewrite -Nat2Z.inj_lt. apply Nats.ltn_lt. rewrite subn1 ltn_predL. auto.
    }
    apply Z.lt_le_incl. exact goal'.
    apply Nats.leq_le. auto.
Qed.

Lemma uelen_can_represent_bias : forall elen mlen, elen > 1 -> mlen > 1 ->
                                  (bias elen >= - 2 ^ Z.of_nat (unpack_elen mlen elen))%Z /\
                                  (bias elen < 2 ^ Z.of_nat (unpack_elen mlen elen))%Z. 
Proof.
Admitted.


Lemma uelen_can_represent_min_normal_e : forall elen mlen, elen > 1 -> mlen > 1 ->
                                          (min_normal_e elen >= - 2 ^ Z.of_nat (unpack_elen mlen elen))%Z /\
                                          (min_normal_e elen < 2 ^ Z.of_nat (unpack_elen mlen elen))%Z. 
Proof.
Admitted.


Lemma to_Z_from_Z : forall n z,  (z >= -(2 ^ (Z.of_nat n)))%Z /\ (z < 2 ^ (Z.of_nat n))%Z -> to_Z (from_Z n z) = z. 
Proof.
Admitted.

Lemma word_blasting_fp_bexp_semantics_equivalence_isInfinite :
  forall (fe : Fq2bvq.fp_exp),
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_exp fe te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1,
            valid_gen_var gen_var ->
              (te1, g1, es1, ubf1, wb_elen1, wb_mlen1) = word_blast_exp gen_var g0 es0 te0 fe ->
                  forall s1 : SSAStore.t,
                    well_formed_bexps es1 te1 && Fq2bvq.well_formed_unpackedbf ubf1 te1 ->
                    conformed_bexps es1 s1 te1 && Fq2bvq.conform_unpackedbf ubf1 s1 te1 ->
                    eval_bexps es1 s1 ->
                      forall pack_s1 pack_e1 pack_m1, 
                        (pack_s1, pack_e1, pack_m1) = pack wb_mlen1 wb_elen1 ubf1 ->
                          forall smt_s1 smt_e1 smt_m1 elen1 mlen1,
                            eval_fp_exp fe s0 (SMTLIBfp.ieee754_fp smt_s1 smt_e1 smt_m1) elen1 mlen1 ->
                            elen1 = wb_elen1 /\
                            mlen1 = wb_mlen1 /\
                            smt_s1 = (QFBV.eval_exp pack_s1 s1) /\ 
                            smt_e1 = (QFBV.eval_exp pack_e1 s1) /\ 
                            smt_m1 = (QFBV.eval_exp pack_m1 s1)) ->
    forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
      Fq2bvq.well_formed_fp_bexp (Fq2bvq.FBunop Fq2bvq.FUisInfinite fe) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' b,
              valid_gen_var gen_var ->
                (te', g', es', b) = word_blast_bexp gen_var g es te (Fq2bvq.FBunop Fq2bvq.FUisInfinite fe) ->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && QFBV.well_formed_bexp b te' ->
                    conformed_bexps es' s' te' && conform_bexp b s' te' ->
                    eval_bexps es' s' ->
                      forall smt_b, eval_fp_bexp (Fq2bvq.FBunop Fq2bvq.FUisInfinite fe) s smt_b ->
                        smt_b = QFBV.eval_bexp b s'.
Proof.
  move => fe IH te s es g /= Hwf Heswf Hescf Hes gen_var g' te' es' b Hgv wb s' Hwbwf Hwbcf Hes' smt_b Hsmt.
  case Hwb: (word_blast_exp gen_var g es te fe) => [[[[[te1 g1] es1] ubf1] wb_elen1] wb_mlen1].
  rewrite Hwb in wb. inversion wb. symmetry in Hwb.
  inversion Hwf.
  specialize (IH te s es g H4 Heswf Hescf Hes gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb).
  move : (word_blasting_fp_exp_is_wellformed fe te es g H4 Heswf gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb) => Hwbwf1.
  move : (word_blasting_fp_exp_is_conformed fe te s es g H4 Heswf Hescf gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb Hwbwf1) => Hwbcf1.
  destruct Hwbcf1 as [s1 Hwbcf1].
  move : (word_blasting_fp_exp_eval_es fe te s es g H4 Heswf Hescf Hes gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb s1 Hwbwf1 Hwbcf1) => Hes1.
  specialize (IH s1 Hwbwf1 Hwbcf1 Hes1).
  case Hpack1: (pack wb_mlen1 wb_elen1 ubf1) => [[pack_s1 pack_e1] pack_m1]. symmetry in Hpack1.
  specialize (IH pack_s1 pack_e1 pack_m1 Hpack1).
  inversion Hsmt. subst. inversion H9. subst.
  specialize (IH s0 e m elen mlen H6). inversion IH.
  assert (Helen : elen = wb_elen1). apply IH.
  assert (Hmlen : mlen = wb_mlen1). apply IH.
  assert (Hs : s0 = QFBV.eval_exp pack_s1 s1). apply IH.
  assert (He : e = QFBV.eval_exp pack_e1 s1). apply IH.
  assert (Hm : m = QFBV.eval_exp pack_m1 s1). apply IH.
  unfold WBClassify.isInfinite_unpackedbf. simpl.
  inversion Hpack1. 
  rewrite H5 in He. rewrite H7 in Hm. 
  rewrite He Hm. simpl. 
  assert (Hwbelen : wb_elen1 > 0). 
  + inversion H0. rewrite -Helen. auto.
  assert (Hwbmlen : wb_mlen1 > 0).
  + inversion H0. rewrite -Hmlen. auto.
  assert (is_ones_zeros_false : forall n, n > 0 -> is_ones (zeros n) = false).
  + destruct n. auto. auto.
  assert (is_zero_ones_false : forall n, n > 0 -> is_zero (ones n) = false). 
  + destruct n. auto. auto.
  assert (Hinf_flag' : QFBV.eval_bexp (inf_flag ubf1) s' = QFBV.eval_bexp (inf_flag ubf1) s1). admit.
  rewrite Hinf_flag'. case Hnan : (QFBV.eval_bexp (nan_flag ubf1) s1). simpl.
  + rewrite ones_is_ones. simpl. rewrite is_zero_ones_false.
    move : (word_blasting_fp_exp_flag_exclusive fe te s es g H4 Heswf Hescf Hes gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb s1 Hwbwf1 Hwbcf1) => Hflag_exclusive.
    inversion Hflag_exclusive. symmetry. apply H2. inversion H2. 
    rewrite Hnan in H8. apply proj1 in H8. discriminate H8.
    rewrite Hnan in H8. inversion H8. apply proj1 in H10. discriminate H10. apply proj1 in H10. discriminate H10.
    apply Hwbmlen. 
  + simpl. case Hinf : (QFBV.eval_bexp (inf_flag ubf1) s1). simpl.
    rewrite ones_is_ones. rewrite zeros_is_zero. auto.
    case Hzero : (QFBV.eval_bexp (zero_flag ubf1) s1). simpl.
    rewrite is_ones_zeros_false. apply Bool.andb_false_l. apply Hwbelen.
    case Hnormal :      
      (sleB
         (sext
            (unpack_elen wb_mlen1 wb_elen1 -
             unpack_elen wb_mlen1 wb_elen1)
            (unpack_elen wb_mlen1 wb_elen1) -bits
            of Z (min_normal_e wb_elen1)%bits)
         (QFBV.eval_exp (un_e ubf1) s1) &&
       sleB (QFBV.eval_exp (un_e ubf1) s1)
         (sext
            (unpack_elen wb_mlen1 wb_elen1 -
             unpack_elen wb_mlen1 wb_elen1)
            (unpack_elen wb_mlen1 wb_elen1) -bits
            of Z (max_normal_e wb_elen1)%bits)). replace (false || false) with false by auto.
    {
       assert (He' : (is_ones
                      (low wb_elen1
                         (QFBV.eval_exp (un_e ubf1) s1 +#
                          (unpack_elen wb_mlen1 wb_elen1) -bits
                          of Z (bias wb_elen1))%bits) = false)). admit. (* copy proof of isNaN *)
       rewrite He' //.
    }
    replace (false || false) with false by auto. rewrite is_ones_zeros_false.  
    apply Bool.andb_false_l. apply Hwbelen.
Admitted.

Lemma word_blasting_fp_bexp_semantics_equivalence_isZero :
  forall (fe : Fq2bvq.fp_exp),
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_exp fe te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1,
            valid_gen_var gen_var ->
              (te1, g1, es1, ubf1, wb_elen1, wb_mlen1) = word_blast_exp gen_var g0 es0 te0 fe ->
                  forall s1 : SSAStore.t,
                    well_formed_bexps es1 te1 && Fq2bvq.well_formed_unpackedbf ubf1 te1 ->
                    conformed_bexps es1 s1 te1 && Fq2bvq.conform_unpackedbf ubf1 s1 te1 ->
                    eval_bexps es1 s1 ->
                      forall pack_s1 pack_e1 pack_m1, 
                        (pack_s1, pack_e1, pack_m1) = pack wb_mlen1 wb_elen1 ubf1 ->
                          forall smt_s1 smt_e1 smt_m1 elen1 mlen1,
                            eval_fp_exp fe s0 (SMTLIBfp.ieee754_fp smt_s1 smt_e1 smt_m1) elen1 mlen1 ->
                            elen1 = wb_elen1 /\
                            mlen1 = wb_mlen1 /\
                            smt_s1 = (QFBV.eval_exp pack_s1 s1) /\ 
                            smt_e1 = (QFBV.eval_exp pack_e1 s1) /\ 
                            smt_m1 = (QFBV.eval_exp pack_m1 s1)) ->
    forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
      Fq2bvq.well_formed_fp_bexp (Fq2bvq.FBunop Fq2bvq.FUisZero fe) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' b,
              valid_gen_var gen_var ->
                (te', g', es', b) = word_blast_bexp gen_var g es te (Fq2bvq.FBunop Fq2bvq.FUisZero fe) ->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && QFBV.well_formed_bexp b te' ->
                    conformed_bexps es' s' te' && conform_bexp b s' te' ->
                    eval_bexps es' s' ->
                      forall smt_b, eval_fp_bexp (Fq2bvq.FBunop Fq2bvq.FUisZero fe) s smt_b ->
                        smt_b = QFBV.eval_bexp b s'.
Proof.
  move => fe IH te s es g /= Hwf Heswf Hescf Hes gen_var g' te' es' b Hgv wb s' Hwbwf Hwbcf Hes' smt_b Hsmt.
  case Hwb: (word_blast_exp gen_var g es te fe) => [[[[[te1 g1] es1] ubf1] wb_elen1] wb_mlen1].
  rewrite Hwb in wb. inversion wb. symmetry in Hwb.
  inversion Hwf.
  specialize (IH te s es g H4 Heswf Hescf Hes gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb).
  move : (word_blasting_fp_exp_is_wellformed fe te es g H4 Heswf gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb) => Hwbwf1.
  move : (word_blasting_fp_exp_is_conformed fe te s es g H4 Heswf Hescf gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb Hwbwf1) => Hwbcf1.
  destruct Hwbcf1 as [s1 Hwbcf1].
  move : (word_blasting_fp_exp_eval_es fe te s es g H4 Heswf Hescf Hes gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb s1 Hwbwf1 Hwbcf1) => Hes1.
  specialize (IH s1 Hwbwf1 Hwbcf1 Hes1).
  case Hpack1: (pack wb_mlen1 wb_elen1 ubf1) => [[pack_s1 pack_e1] pack_m1]. symmetry in Hpack1.
  specialize (IH pack_s1 pack_e1 pack_m1 Hpack1).
  inversion Hsmt. subst. inversion H9. subst.
  specialize (IH s0 e m elen mlen H6). inversion IH.
  assert (Helen : elen = wb_elen1). apply IH.
  assert (Hmlen : mlen = wb_mlen1). apply IH.
  assert (Hs : s0 = QFBV.eval_exp pack_s1 s1). apply IH.
  assert (He : e = QFBV.eval_exp pack_e1 s1). apply IH.
  assert (Hm : m = QFBV.eval_exp pack_m1 s1). apply IH.
  unfold WBClassify.isInfinite_unpackedbf. simpl.
  inversion Hpack1. 
  rewrite H5 in He. rewrite H7 in Hm. 
  rewrite He Hm. simpl. 
  assert (Hwbelen : wb_elen1 > 0). 
  + inversion H0. rewrite -Helen. auto.
  assert (Hwbmlen : wb_mlen1 > 0).
  + inversion H0. rewrite -Hmlen. auto.
  assert (is_ones_zeros_false : forall n, n > 0 -> is_ones (zeros n) = false).
  + destruct n. auto. auto.
  assert (is_zero_ones_false : forall n, n > 0 -> is_zero (ones n) = false). 
  + destruct n. auto. auto.
  assert (Hzero_flag' : QFBV.eval_bexp (zero_flag ubf1) s' = QFBV.eval_bexp (zero_flag ubf1) s1). admit.
  rewrite Hzero_flag'. case Hnan : (QFBV.eval_bexp (nan_flag ubf1) s1). simpl.
  + rewrite is_zero_ones_false. simpl.
    move : (word_blasting_fp_exp_flag_exclusive fe te s es g H4 Heswf Hescf Hes gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb s1 Hwbwf1 Hwbcf1) => Hflag_exclusive.
    inversion Hflag_exclusive. symmetry. apply H2. inversion H2. 
    rewrite Hnan in H8. apply proj1 in H8. discriminate H8.
    rewrite Hnan in H8. inversion H8. apply proj1 in H10. discriminate H10. apply proj1 in H10. discriminate H10.
    apply Hwbelen. 
  + case Hinf : (QFBV.eval_bexp (inf_flag ubf1) s1). simpl.
    - rewrite is_zero_ones_false. simpl. 
      move : (word_blasting_fp_exp_flag_exclusive fe te s es g H4 Heswf Hescf Hes gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb s1 Hwbwf1 Hwbcf1) => Hflag_exclusive.
      inversion Hflag_exclusive. 
      rewrite Hnan in H2. apply proj1 in H2. discriminate H2.
      inversion H2. symmetry. apply H8.  
      rewrite Hinf in H8. inversion H8. inversion H10. apply proj1 in H12. discriminate H12.
      inversion H10. apply proj1 in H12. discriminate H12.
      apply Hwbelen. 
    - case Hzero : (QFBV.eval_bexp (zero_flag ubf1) s1). simpl.
      rewrite zeros_is_zero zeros_is_zero //. 
      case Hnormal :      
        (sleB
           (sext
              (unpack_elen wb_mlen1 wb_elen1 -
               unpack_elen wb_mlen1 wb_elen1)
              (unpack_elen wb_mlen1 wb_elen1) -bits
              of Z (min_normal_e wb_elen1)%bits)
           (QFBV.eval_exp (un_e ubf1) s1) &&
         sleB (QFBV.eval_exp (un_e ubf1) s1)
           (sext
              (unpack_elen wb_mlen1 wb_elen1 -
               unpack_elen wb_mlen1 wb_elen1)
              (unpack_elen wb_mlen1 wb_elen1) -bits
              of Z (max_normal_e wb_elen1)%bits)). replace (false || false) with false by auto.
      {
         assert (He' : (is_zero
                        (low wb_elen1
                           (QFBV.eval_exp (un_e ubf1) s1 +#
                            (unpack_elen wb_mlen1 wb_elen1) -bits
                            of Z (bias wb_elen1))%bits) = false)). 
         {
            apply (Bool.negb_true_iff). apply (Bool.Is_true_eq_true). apply (Bool.negb_prop_intro).
            move : Hnormal. apply contraPnot. 
            move => He'. 
            replace (unpack_elen wb_mlen1 wb_elen1 - unpack_elen wb_mlen1 wb_elen1) with 0 by rewrite subnn //.
            rewrite sext0 sext0.
            apply Bool.not_true_iff_false. apply Bool.andb_false_iff. 
             case Huelen_eq_elen : ((unpack_elen wb_mlen1 wb_elen1) =? wb_elen1).
             {
                left.
                rewrite to_Z_sleB_eqn. apply negbTE. rewrite -BinInt.Z.ltb_antisym. apply /ZAriths.Z_ltP.
                apply (Zorder.Zplus_lt_reg_r (to_Z (QFBV.eval_exp (un_e ubf1) s1))
                                             (to_Z (unpack_elen wb_mlen1 wb_elen1) -bits of Z (min_normal_e wb_elen1)%bits) 
                                             (to_Z (unpack_elen wb_mlen1 wb_elen1) -bits of Z (bias wb_elen1)%bits)).
                rewrite -bv2z_add_signed.
                move : cat_low_high => Hcat.
                specialize (Hcat (QFBV.eval_exp (un_e ubf1) s1 +#
              (unpack_elen wb_mlen1 wb_elen1) -bits of Z (bias wb_elen1))%bits wb_elen1 ((unpack_elen wb_mlen1 wb_elen1) - wb_elen1)).
                assert (Hcat_size : wb_elen1 + (unpack_elen wb_mlen1 wb_elen1 - wb_elen1) =
               size
                 (QFBV.eval_exp (un_e ubf1) s1 +#
                  (unpack_elen wb_mlen1 wb_elen1) -bits of Z (bias wb_elen1))%bits).
                  + rewrite subnKC. rewrite size_addB size_from_Z. 
                    assert (Huesize : size (QFBV.eval_exp (un_e ubf1) s1) = (unpack_elen wb_mlen1 wb_elen1)). admit.
                    rewrite Huesize minnE subnn subn0 //.
                    assert (Hwbelen1' : 1 < wb_elen1). inversion H0. rewrite Helen in H12. exact H12.
                    assert (Hwbmlen1' : 1 < wb_mlen1). inversion H0. rewrite Hmlen in H11. exact H11.
                    apply (uelen_ge_elen wb_elen1 wb_mlen1 Hwbelen1' Hwbmlen1').
                specialize (Hcat Hcat_size).
                rewrite -Hcat.
                
                apply beq_nat_true in Huelen_eq_elen.
                rewrite Huelen_eq_elen subnn high0 cats0 /=.
               
                apply Bool.Is_true_eq_true in He'. 
                apply is_zero_zeros in He'. rewrite size_low in He'.
                rewrite Huelen_eq_elen in He'. rewrite He'.
                rewrite to_Z_from_Z. rewrite to_Z_from_Z. 
                unfold min_normal_e. rewrite Z.opp_sub_distr Z.add_opp_l Z.sub_add.
                rewrite to_Z_zeros. lia. 
                + apply (elen_can_represent_bias wb_elen1 wb_mlen1).
                  assert (Hwbelen1' : 1 < wb_elen1). inversion H0. rewrite Helen in H12. exact H12. exact Hwbelen1'.
                  assert (Hwbmlen1' : 1 < wb_mlen1). inversion H0. rewrite Hmlen in H11. exact H11. exact Hwbmlen1'.
                + unfold min_normal_e. unfold bias. unfold elen_Z.
                  replace (- (2 ^ (Z.of_nat wb_elen1 - 1) - 1 - 1))%Z with
                    (- (2 ^ (Z.of_nat wb_elen1 - 1) - 2))%Z by lia.
                  replace 1%Z with (Z.of_nat 1)%Z by auto.
                  rewrite -Nat2Z.inj_sub. rewrite -Nats.subn_sub. 
                  split.
                  - apply Z.le_ge. apply Z.opp_le_mono. rewrite Z.opp_involutive Z.opp_involutive.
                    + (* 2^(e-1)-2 <= 2^e *)
                      admit.
                    + apply (Z.le_lt_trans (- (2 ^ Z.of_nat (wb_elen1 - 1) - 2))%Z 0%Z (2 ^ Z.of_nat wb_elen1)%Z).
                      * (* -(2^(e-1)-2) <= 0, e > 1 *)
                        admit.
                      * apply ZAriths.zero_lt_two_power_of_nat.
                    + assert (Hwbelen1' : 1 < wb_elen1). inversion H0. rewrite Helen in H12. exact H12.
                      apply Nats.ltn_lt. auto.
                    + rewrite size_from_Z. admit.
                    + admit.
                    + rewrite size_from_Z. admit.
              }
            case Hminus : (to_Z
   (high (unpack_elen wb_mlen1 wb_elen1 - wb_elen1)
      (QFBV.eval_exp (un_e ubf1) s1 +#
       (unpack_elen wb_mlen1 wb_elen1) -bits of Z (bias wb_elen1))%bits) <=? 0)%Z.  
             {
                left.
                rewrite to_Z_sleB_eqn. apply negbTE. rewrite -BinInt.Z.ltb_antisym. apply /ZAriths.Z_ltP.
                apply (Zorder.Zplus_lt_reg_r (to_Z (QFBV.eval_exp (un_e ubf1) s1))
                                             (to_Z (unpack_elen wb_mlen1 wb_elen1) -bits of Z (min_normal_e wb_elen1)%bits) 
                                             (to_Z (unpack_elen wb_mlen1 wb_elen1) -bits of Z (bias wb_elen1)%bits)).
                rewrite -bv2z_add_signed.
                move : cat_low_high => Hcat.
                specialize (Hcat (QFBV.eval_exp (un_e ubf1) s1 +#
              (unpack_elen wb_mlen1 wb_elen1) -bits of Z (bias wb_elen1))%bits wb_elen1 ((unpack_elen wb_mlen1 wb_elen1) - wb_elen1)).
                assert (Hcat_size : wb_elen1 + (unpack_elen wb_mlen1 wb_elen1 - wb_elen1) =
               size
                 (QFBV.eval_exp (un_e ubf1) s1 +#
                  (unpack_elen wb_mlen1 wb_elen1) -bits of Z (bias wb_elen1))%bits).
                  + rewrite subnKC. rewrite size_addB size_from_Z. 
                    assert (Huesize : size (QFBV.eval_exp (un_e ubf1) s1) = (unpack_elen wb_mlen1 wb_elen1)). admit.
                    rewrite Huesize minnE subnn subn0 //.
                    assert (Hwbelen1' : 1 < wb_elen1). inversion H0. rewrite Helen in H12. exact H12.
                    assert (Hwbmlen1' : 1 < wb_mlen1). inversion H0. rewrite Hmlen in H11. exact H11.
                    apply (uelen_ge_elen wb_elen1 wb_mlen1 Hwbelen1' Hwbmlen1').
                specialize (Hcat Hcat_size).
                rewrite -Hcat. rewrite to_Z_cat. 
                apply Bool.Is_true_eq_true in He'. 
                apply is_zero_zeros in He'. rewrite size_low in He'. rewrite He'. unfold min_normal_e.
                rewrite to_Zpos_zeros size_zeros.
                rewrite to_Z_from_Z. rewrite to_Z_from_Z. rewrite Z.opp_sub_distr. 
                rewrite Zplus_assoc_reverse Z.add_1_l Z.add_succ_r Z.add_opp_diag_l -Z.one_succ.
                simpl.

                move /ZAriths.Z_leP : Hminus. move => Hminus.
                move : (Z.mul_nonpos_nonneg _ _ Hminus (Z.lt_le_incl _ _ (pow2_nat2z_gt0 wb_elen1))) => Hminus2.
                apply Zle_lt_succ in Hminus2. simpl in Hminus2. exact Hminus2.
                + apply (uelen_can_represent_bias wb_elen1 wb_mlen1).
                  assert (Hwbelen1' : 1 < wb_elen1). inversion H0. rewrite Helen in H12. exact H12. exact Hwbelen1'.
                  assert (Hwbmlen1' : 1 < wb_mlen1). inversion H0. rewrite Hmlen in H11. exact H11. exact Hwbmlen1'.
                + replace (- (bias wb_elen1 - 1))%Z with (min_normal_e wb_elen1).
                  apply (uelen_can_represent_min_normal_e wb_elen1 wb_mlen1).
                  assert (Hwbelen1' : 1 < wb_elen1). inversion H0. rewrite Helen in H12. exact H12. exact Hwbelen1'.
                  assert (Hwbmlen1' : 1 < wb_mlen1). inversion H0. rewrite Hmlen in H11. exact H11. exact Hwbmlen1'.
                  unfold min_normal_e. auto.
                + rewrite size_high. 
                  apply beq_nat_false in Huelen_eq_elen. 
                  rewrite subn_gt0.
                  assert (Hwbelen1' : 1 < wb_elen1). inversion H0. rewrite Helen in H12. exact H12.
                  assert (Hwbmlen1' : 1 < wb_mlen1). inversion H0. rewrite Hmlen in H11. exact H11.
                  move : (uelen_ge_elen wb_elen1 wb_mlen1 Hwbelen1' Hwbmlen1'). move => uelen_ge_elen.
                  apply Nats.leq_le in uelen_ge_elen.
                  apply nesym in Huelen_eq_elen.
                  apply Nats.lt_ltn. apply Nat.le_neq. split. auto. auto.
                + rewrite size_from_Z. admit.
                + admit.
                + rewrite size_from_Z. admit.
             }
             {
               right. apply Z.leb_gt in Hminus.
               rewrite to_Z_sleB_eqn. apply negbTE. rewrite -BinInt.Z.ltb_antisym. apply /ZAriths.Z_ltP.
               apply (Zorder.Zplus_lt_reg_r (to_Z (unpack_elen wb_mlen1 wb_elen1) -bits of Z (max_normal_e wb_elen1)%bits) 
                                            (to_Z (QFBV.eval_exp (un_e ubf1) s1))
                                            (to_Z (unpack_elen wb_mlen1 wb_elen1) -bits of Z (bias wb_elen1)%bits)).
               replace (to_Z (QFBV.eval_exp (un_e ubf1) s1) +
         to_Z (unpack_elen wb_mlen1 wb_elen1) -bits of Z (bias wb_elen1)%bits)%Z with
                (to_Z
           (QFBV.eval_exp (un_e ubf1) s1 +# (unpack_elen wb_mlen1 wb_elen1) -bits of Z (bias wb_elen1))%bits)%Z.
               move : cat_low_high => Hcat.
               specialize (Hcat (QFBV.eval_exp (un_e ubf1) s1 +#
                    (unpack_elen wb_mlen1 wb_elen1) -bits of Z (bias wb_elen1))%bits wb_elen1 ((unpack_elen wb_mlen1 wb_elen1) - wb_elen1)).
               assert (Hcat_size : wb_elen1 + (unpack_elen wb_mlen1 wb_elen1 - wb_elen1) =
               size
                 (QFBV.eval_exp (un_e ubf1) s1 +#
                  (unpack_elen wb_mlen1 wb_elen1) -bits of Z (bias wb_elen1))%bits).
                  + rewrite subnKC. rewrite size_addB size_from_Z. 
                    assert (Huesize : size (QFBV.eval_exp (un_e ubf1) s1) = (unpack_elen wb_mlen1 wb_elen1)). admit.
                    rewrite Huesize minnE subnn subn0 //.
                    assert (Hwbelen1' : 1 < wb_elen1). inversion H0. rewrite Helen in H12. exact H12.
                    assert (Hwbmlen1' : 1 < wb_mlen1). inversion H0. rewrite Hmlen in H11. exact H11.
                    apply (uelen_ge_elen wb_elen1 wb_mlen1 Hwbelen1' Hwbmlen1').
                specialize (Hcat Hcat_size).
                rewrite -Hcat.
                {
                  rewrite to_Z_cat. 
                  apply Bool.Is_true_eq_true in He'.
                  apply is_zero_zeros in He'. rewrite size_low in He'. rewrite He'. unfold max_normal_e. 
                  rewrite to_Zpos_zeros size_zeros Z.add_0_l.
                  rewrite to_Z_from_Z. rewrite Z.add_diag. 
                  move : Hminus. 
                  unfold bias. unfold elen_Z. 
                  replace (2 * (2 ^ (Z.of_nat wb_elen1 - 1) - 1))%Z with
                    (2 * (2 ^ (Z.of_nat wb_elen1 - 1)) - 2)%Z by lia. 
                  replace (Z.of_nat wb_elen1 - 1)%Z with (Z.of_nat (wb_elen1 - 1))%Z.
                  rewrite -Z.pow_succ_r. rewrite -Nat2Z.inj_succ.
                  rewrite subn1 -S_pred_pos.
                  move => Hminus.
                  apply (Z.lt_trans (2 ^ Z.of_nat wb_elen1 - 2)%Z (2 ^ Z.of_nat wb_elen1 -1)%Z).
                  lia.
                  rewrite Z.sub_1_r. apply Z.lt_pred_le. 
                  rewrite Z.mul_comm. apply Z.le_mul_diag_r.
                  apply pow2_nat2z_gt0.
                  apply Zlt_le_succ in Hminus. simpl in Hminus. exact Hminus.
                  + apply Nats.ltn_lt. exact Hwbelen.
                  + apply Nat2Z.is_nonneg.
                  + replace 1%Z with (Z.of_nat 1)%Z by auto. rewrite Nat2Z.inj_sub //.
                  + assert (Hwbelen1' : 1 < wb_elen1). inversion H0. rewrite Helen in H12. exact H12.
                    apply Nats.ltn_lt in Hwbelen1'. apply Nat.lt_le_incl. exact Hwbelen1'.
                  + apply uelen_can_represent_bias.
                    assert (Hwbelen1' : 1 < wb_elen1). inversion H0. rewrite Helen in H12. exact H12.
                    exact Hwbelen1'.
                    assert (Hwbmlen1' : 1 < wb_mlen1). inversion H0. rewrite Hmlen in H11. exact H11.
                    exact Hwbmlen1'.
                  + rewrite size_high.
                  + assert (Hwbelen1' : 1 < wb_elen1). inversion H0. rewrite Helen in H12. exact H12.
                    assert (Hwbmlen1' : 1 < wb_mlen1). inversion H0. rewrite Hmlen in H11. exact H11.
                    move : (uelen_ge_elen wb_elen1 wb_mlen1 Hwbelen1' Hwbmlen1'). move => uelen_ge_elen.
                    apply Nats.leq_le in uelen_ge_elen.
                    apply Nats.lt_ltn. apply Nat.le_neq. split. lia. admit. (* by Huelen_eq_elen *)
                }
                + rewrite -bv2z_add_signed.
                  - auto.
                  - rewrite size_from_Z //.
                  - admit.
                  - admit.
                  - rewrite size_from_Z. admit.
             }
         }
         rewrite He' //.
      }
      (* subnormal case *)
      replace (false || false) with false by auto. rewrite zeros_is_zero Bool.andb_true_l.
      case Hif1 : (unpack_elen wb_mlen1 wb_elen1 <= unpack_mlen wb_mlen1). simpl.
      {
        admit.
      }
      {
        admit.
      }
Admitted.

Lemma word_blasting_fp_bexp_semantics_equivalence_isNaN :
  forall (fe : Fq2bvq.fp_exp),
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_exp fe te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1,
            valid_gen_var gen_var ->
              (te1, g1, es1, ubf1, wb_elen1, wb_mlen1) = word_blast_exp gen_var g0 es0 te0 fe ->
                  forall s1 : SSAStore.t,
                    well_formed_bexps es1 te1 && Fq2bvq.well_formed_unpackedbf ubf1 te1 ->
                    conformed_bexps es1 s1 te1 && Fq2bvq.conform_unpackedbf ubf1 s1 te1 ->
                    eval_bexps es1 s1 ->
                      forall pack_s1 pack_e1 pack_m1, 
                        (pack_s1, pack_e1, pack_m1) = pack wb_mlen1 wb_elen1 ubf1 ->
                          forall smt_s1 smt_e1 smt_m1 elen1 mlen1,
                            eval_fp_exp fe s0 (SMTLIBfp.ieee754_fp smt_s1 smt_e1 smt_m1) elen1 mlen1 ->
                            elen1 = wb_elen1 /\
                            mlen1 = wb_mlen1 /\
                            smt_s1 = (QFBV.eval_exp pack_s1 s1) /\ 
                            smt_e1 = (QFBV.eval_exp pack_e1 s1) /\ 
                            smt_m1 = (QFBV.eval_exp pack_m1 s1)) ->
    forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
      Fq2bvq.well_formed_fp_bexp (Fq2bvq.FBunop Fq2bvq.FUisNaN fe) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' b,
              valid_gen_var gen_var ->
                (te', g', es', b) = word_blast_bexp gen_var g es te (Fq2bvq.FBunop Fq2bvq.FUisNaN fe) ->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && QFBV.well_formed_bexp b te' ->
                    conformed_bexps es' s' te' && conform_bexp b s' te' ->
                    eval_bexps es' s' ->
                      forall smt_b, eval_fp_bexp (Fq2bvq.FBunop Fq2bvq.FUisNaN fe) s smt_b ->
                        smt_b = QFBV.eval_bexp b s'.
Proof.  
  move => fe IH te s es g /= Hwf Heswf Hescf Hes gen_var g' te' es' b Hgv wb s' Hwbwf Hwbcf Hes' smt_b Hsmt.
  case Hwb: (word_blast_exp gen_var g es te fe) => [[[[[te1 g1] es1] ubf1] wb_elen1] wb_mlen1].
  rewrite Hwb in wb. inversion wb. symmetry in Hwb.
  inversion Hwf.
  specialize (IH te s es g H4 Heswf Hescf Hes gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb).
  move : (word_blasting_fp_exp_is_wellformed fe te es g H4 Heswf gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb) => Hwbwf1.
  move : (word_blasting_fp_exp_is_conformed fe te s es g H4 Heswf Hescf gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb Hwbwf1) => Hwbcf1.
  destruct Hwbcf1 as [s1 Hwbcf1].
  move : (word_blasting_fp_exp_eval_es fe te s es g H4 Heswf Hescf Hes gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb s1 Hwbwf1 Hwbcf1) => Hes1.
  specialize (IH s1 Hwbwf1 Hwbcf1 Hes1).
  case Hpack1: (pack wb_mlen1 wb_elen1 ubf1) => [[pack_s1 pack_e1] pack_m1]. symmetry in Hpack1.
  specialize (IH pack_s1 pack_e1 pack_m1 Hpack1).
  inversion Hsmt. subst. inversion H9. subst.
  specialize (IH s0 e m elen mlen H6). inversion IH.
  assert (Helen : elen = wb_elen1). apply IH.
  assert (Hmlen : mlen = wb_mlen1). apply IH.
  assert (Hs : s0 = QFBV.eval_exp pack_s1 s1). apply IH.
  assert (He : e = QFBV.eval_exp pack_e1 s1). apply IH.
  assert (Hm : m = QFBV.eval_exp pack_m1 s1). apply IH.
  unfold WBClassify.isNaN_unpackedbf. simpl.
  inversion Hpack1. 
  rewrite H5 in He. rewrite H7 in Hm. 
  rewrite He Hm. simpl. 
  assert (Hwbelen : wb_elen1 > 0). 
  + inversion H0. rewrite -Helen. auto.
  assert (Hwbmlen : wb_mlen1 > 0).
  + inversion H0. rewrite -Hmlen. auto.
  assert (is_ones_zeros_false : forall n, n > 0 -> is_ones (zeros n) = false).
  + destruct n. auto. auto.
  assert (is_zero_ones_false : forall n, n > 0 -> is_zero (ones n) = false). 
  + destruct n. auto. auto.
  
  assert (Hnan_flag' : QFBV.eval_bexp (nan_flag ubf1) s' = QFBV.eval_bexp (nan_flag ubf1) s1). admit.
  
  rewrite Hnan_flag'. case Hnan : (QFBV.eval_bexp (nan_flag ubf1) s1). simpl.
  rewrite ones_is_ones. simpl. rewrite is_zero_ones_false. auto. apply Hwbmlen.
  case Hinf : (QFBV.eval_bexp (inf_flag ubf1) s1). simpl.
  rewrite ones_is_ones. rewrite zeros_is_zero. auto.
  case Hzero : (QFBV.eval_bexp (zero_flag ubf1) s1). simpl.
  rewrite zeros_is_zero. replace (~~ true) with false by auto. apply Bool.andb_false_r.
  case Hnormal :      
    (sleB
       (sext
          (unpack_elen wb_mlen1 wb_elen1 -
           unpack_elen wb_mlen1 wb_elen1)
          (unpack_elen wb_mlen1 wb_elen1) -bits
          of Z (min_normal_e wb_elen1)%bits)
       (QFBV.eval_exp (un_e ubf1) s1) &&
     sleB (QFBV.eval_exp (un_e ubf1) s1)
       (sext
          (unpack_elen wb_mlen1 wb_elen1 -
           unpack_elen wb_mlen1 wb_elen1)
          (unpack_elen wb_mlen1 wb_elen1) -bits
          of Z (max_normal_e wb_elen1)%bits)). replace (false || false) with false by auto. 
  { 
    assert (He' : (is_ones
                    (low wb_elen1
                       (QFBV.eval_exp (un_e ubf1) s1 +#
                        (unpack_elen wb_mlen1 wb_elen1) -bits
                        of Z (bias wb_elen1))%bits) = false)). 
    {
      apply (Bool.negb_true_iff). apply (Bool.Is_true_eq_true). apply (Bool.negb_prop_intro). 
      move : Hnormal. apply contraPnot. 
      move => He'. 
      replace (unpack_elen wb_mlen1 wb_elen1 - unpack_elen wb_mlen1 wb_elen1) with 0 by rewrite subnn //.
      rewrite sext0 sext0.
      apply Bool.not_true_iff_false. apply Bool.andb_false_iff. 
      case Huelen_eq_elen : ((unpack_elen wb_mlen1 wb_elen1) =? wb_elen1).
       {
          left.
          rewrite to_Z_sleB_eqn. apply negbTE. rewrite -BinInt.Z.ltb_antisym. apply /ZAriths.Z_ltP.
          apply (Zorder.Zplus_lt_reg_r (to_Z (QFBV.eval_exp (un_e ubf1) s1))
                                       (to_Z (unpack_elen wb_mlen1 wb_elen1) -bits of Z (min_normal_e wb_elen1)%bits) 
                                       (to_Z (unpack_elen wb_mlen1 wb_elen1) -bits of Z (bias wb_elen1)%bits)).
          rewrite -bv2z_add_signed.
          move : cat_low_high => Hcat.
          specialize (Hcat (QFBV.eval_exp (un_e ubf1) s1 +#
        (unpack_elen wb_mlen1 wb_elen1) -bits of Z (bias wb_elen1))%bits wb_elen1 ((unpack_elen wb_mlen1 wb_elen1) - wb_elen1)).
          assert (Hcat_size : wb_elen1 + (unpack_elen wb_mlen1 wb_elen1 - wb_elen1) =
         size
           (QFBV.eval_exp (un_e ubf1) s1 +#
            (unpack_elen wb_mlen1 wb_elen1) -bits of Z (bias wb_elen1))%bits).
            + rewrite subnKC. rewrite size_addB size_from_Z. 
              assert (Huesize : size (QFBV.eval_exp (un_e ubf1) s1) = (unpack_elen wb_mlen1 wb_elen1)). admit.
              rewrite Huesize minnE subnn subn0 //.
              assert (Hwbelen1' : 1 < wb_elen1). inversion H0. rewrite Helen in H12. exact H12.
              assert (Hwbmlen1' : 1 < wb_mlen1). inversion H0. rewrite Hmlen in H11. exact H11.
              apply (uelen_ge_elen wb_elen1 wb_mlen1 Hwbelen1' Hwbmlen1').
          specialize (Hcat Hcat_size).
          rewrite -Hcat.
          apply beq_nat_true in Huelen_eq_elen.
          rewrite Huelen_eq_elen subnn high0 cats0 /=.
          apply Bool.Is_true_eq_true in He'. 
          apply is_ones_ones in He'. rewrite size_low in He'.
          rewrite Huelen_eq_elen in He'. rewrite He'.
          rewrite to_Z_from_Z. rewrite to_Z_from_Z. 
          unfold min_normal_e. rewrite Z.opp_sub_distr Z.add_opp_l Z.sub_add.
          rewrite to_Z_ones. lia. apply Hwbelen.
          + apply (elen_can_represent_bias wb_elen1 wb_mlen1).
            assert (Hwbelen1' : 1 < wb_elen1). inversion H0. rewrite Helen in H12. exact H12. exact Hwbelen1'.
            assert (Hwbmlen1' : 1 < wb_mlen1). inversion H0. rewrite Hmlen in H11. exact H11. exact Hwbmlen1'.
          + unfold min_normal_e. unfold bias. unfold elen_Z.
            replace (- (2 ^ (Z.of_nat wb_elen1 - 1) - 1 - 1))%Z with
              (- (2 ^ (Z.of_nat wb_elen1 - 1) - 2))%Z by lia.
            replace 1%Z with (Z.of_nat 1)%Z by auto.
            rewrite -Nat2Z.inj_sub. rewrite -Nats.subn_sub. 
            split.
            - apply Z.le_ge. apply Z.opp_le_mono. rewrite Z.opp_involutive Z.opp_involutive.
              + (* 2^(e-1)-2 <= 2^e *)
                admit.
              + apply (Z.le_lt_trans (- (2 ^ Z.of_nat (wb_elen1 - 1) - 2))%Z 0%Z (2 ^ Z.of_nat wb_elen1)%Z).
                * (* -(2^(e-1)-2) <= 0, e > 1 *)
                  admit.
                * apply ZAriths.zero_lt_two_power_of_nat.
              + assert (Hwbelen1' : 1 < wb_elen1). inversion H0. rewrite Helen in H12. exact H12.
                apply Nats.ltn_lt. auto.
              + rewrite size_from_Z. admit.
              + admit.
              + rewrite size_from_Z. admit.
        }  
      case Hminus : (to_Z
   (high (unpack_elen wb_mlen1 wb_elen1 - wb_elen1)
      (QFBV.eval_exp (un_e ubf1) s1 +#
       (unpack_elen wb_mlen1 wb_elen1) -bits of Z (bias wb_elen1))%bits) <? 0)%Z.
     {
        left.
        rewrite to_Z_sleB_eqn. apply negbTE. rewrite -BinInt.Z.ltb_antisym. apply /ZAriths.Z_ltP.
        apply (Zorder.Zplus_lt_reg_r (to_Z (QFBV.eval_exp (un_e ubf1) s1))
                                     (to_Z (unpack_elen wb_mlen1 wb_elen1) -bits of Z (min_normal_e wb_elen1)%bits) 
                                     (to_Z (unpack_elen wb_mlen1 wb_elen1) -bits of Z (bias wb_elen1)%bits)).
        rewrite -bv2z_add_signed.
        move : cat_low_high => Hcat.
        specialize (Hcat (QFBV.eval_exp (un_e ubf1) s1 +#
      (unpack_elen wb_mlen1 wb_elen1) -bits of Z (bias wb_elen1))%bits wb_elen1 ((unpack_elen wb_mlen1 wb_elen1) - wb_elen1)).
        assert (Hcat_size : wb_elen1 + (unpack_elen wb_mlen1 wb_elen1 - wb_elen1) =
       size
         (QFBV.eval_exp (un_e ubf1) s1 +#
          (unpack_elen wb_mlen1 wb_elen1) -bits of Z (bias wb_elen1))%bits).
          + rewrite subnKC. rewrite size_addB size_from_Z. 
            assert (Huesize : size (QFBV.eval_exp (un_e ubf1) s1) = (unpack_elen wb_mlen1 wb_elen1)). admit.
            rewrite Huesize minnE subnn subn0 //.
            assert (Hwbelen1' : 1 < wb_elen1). inversion H0. rewrite Helen in H12. exact H12.
            assert (Hwbmlen1' : 1 < wb_mlen1). inversion H0. rewrite Hmlen in H11. exact H11.
            apply (uelen_ge_elen wb_elen1 wb_mlen1 Hwbelen1' Hwbmlen1').
        specialize (Hcat Hcat_size).
        rewrite -Hcat. rewrite to_Z_cat. 
        apply Bool.Is_true_eq_true in He'. 
        apply is_ones_ones in He'. rewrite size_low in He'. rewrite He'. unfold min_normal_e.
        rewrite to_Zpos_ones size_ones.
        rewrite to_Z_from_Z. rewrite to_Z_from_Z. rewrite Z.opp_sub_distr. 
        rewrite Zplus_assoc_reverse Z.add_1_l Z.add_succ_r Z.add_opp_diag_l -Z.one_succ.
        replace (2 ^ Z.of_nat wb_elen1 - 1 +
                   to_Z
                     (high (unpack_elen wb_mlen1 wb_elen1 - wb_elen1)
                        (QFBV.eval_exp (un_e ubf1) s1 +#
                         (unpack_elen wb_mlen1 wb_elen1) -bits of Z (bias wb_elen1))%bits) *
                   2 ^ Z.of_nat wb_elen1)%Z with 
                (2 ^ Z.of_nat wb_elen1 +
                   to_Z
                     (high (unpack_elen wb_mlen1 wb_elen1 - wb_elen1)
                        (QFBV.eval_exp (un_e ubf1) s1 +#
                         (unpack_elen wb_mlen1 wb_elen1) -bits of Z (bias wb_elen1))%bits) *
                   2 ^ Z.of_nat wb_elen1 - 1)%Z by lia.
        rewrite Z.lt_sub_lt_add_l. simpl.
        rewrite Z.mul_comm Zred_factor2. move /ZAriths.Z_ltP : Hminus. move => Hminus.
        move : (Zlt_le_succ _ _ Hminus) => Hminus1. rewrite Z.add_1_l. 
        move : (Z.mul_nonneg_nonpos _ _ (Z.lt_le_incl _ _ (pow2_nat2z_gt0 wb_elen1)) Hminus1) => Hminus2. 
        assert (H0le1 : (0 <= 1)%Z). lia.
        move : (Z.le_trans _ 0 1 Hminus2 H0le1) => Hminus3. 
        move : (Zle_lt_succ _ _ Hminus3) => Hminus4. simpl in Hminus4. exact Hminus4. 
        + apply (uelen_can_represent_bias wb_elen1 wb_mlen1).
          assert (Hwbelen1' : 1 < wb_elen1). inversion H0. rewrite Helen in H12. exact H12. exact Hwbelen1'.
          assert (Hwbmlen1' : 1 < wb_mlen1). inversion H0. rewrite Hmlen in H11. exact H11. exact Hwbmlen1'.
        + replace (- (bias wb_elen1 - 1))%Z with (min_normal_e wb_elen1).
          apply (uelen_can_represent_min_normal_e wb_elen1 wb_mlen1).
          assert (Hwbelen1' : 1 < wb_elen1). inversion H0. rewrite Helen in H12. exact H12. exact Hwbelen1'.
          assert (Hwbmlen1' : 1 < wb_mlen1). inversion H0. rewrite Hmlen in H11. exact H11. exact Hwbmlen1'.
          unfold min_normal_e. auto.
        + rewrite size_high. 
          apply beq_nat_false in Huelen_eq_elen. 
          rewrite subn_gt0.
          assert (Hwbelen1' : 1 < wb_elen1). inversion H0. rewrite Helen in H12. exact H12.
          assert (Hwbmlen1' : 1 < wb_mlen1). inversion H0. rewrite Hmlen in H11. exact H11.
          move : (uelen_ge_elen wb_elen1 wb_mlen1 Hwbelen1' Hwbmlen1'). move => uelen_ge_elen.
          apply Nats.leq_le in uelen_ge_elen.
          apply nesym in Huelen_eq_elen.
          apply Nats.lt_ltn. apply Nat.le_neq. split. auto. auto.
        + rewrite size_from_Z. admit.
        + admit.
        + rewrite size_from_Z. admit.
     }
     {
       right. apply Z.ltb_ge in Hminus.
       rewrite to_Z_sleB_eqn. apply negbTE. rewrite -BinInt.Z.ltb_antisym. apply /ZAriths.Z_ltP.
       apply (Zorder.Zplus_lt_reg_r (to_Z (unpack_elen wb_mlen1 wb_elen1) -bits of Z (max_normal_e wb_elen1)%bits) 
                                    (to_Z (QFBV.eval_exp (un_e ubf1) s1))
                                    (to_Z (unpack_elen wb_mlen1 wb_elen1) -bits of Z (bias wb_elen1)%bits)).
       replace (to_Z (QFBV.eval_exp (un_e ubf1) s1) +
 to_Z (unpack_elen wb_mlen1 wb_elen1) -bits of Z (bias wb_elen1)%bits)%Z with
        (to_Z
   (QFBV.eval_exp (un_e ubf1) s1 +# (unpack_elen wb_mlen1 wb_elen1) -bits of Z (bias wb_elen1))%bits)%Z.
       move : cat_low_high => Hcat.
       specialize (Hcat (QFBV.eval_exp (un_e ubf1) s1 +#
            (unpack_elen wb_mlen1 wb_elen1) -bits of Z (bias wb_elen1))%bits wb_elen1 ((unpack_elen wb_mlen1 wb_elen1) - wb_elen1)).
       assert (Hcat_size : wb_elen1 + (unpack_elen wb_mlen1 wb_elen1 - wb_elen1) =
       size
         (QFBV.eval_exp (un_e ubf1) s1 +#
          (unpack_elen wb_mlen1 wb_elen1) -bits of Z (bias wb_elen1))%bits).
          + rewrite subnKC. rewrite size_addB size_from_Z. 
            assert (Huesize : size (QFBV.eval_exp (un_e ubf1) s1) = (unpack_elen wb_mlen1 wb_elen1)). admit.
            rewrite Huesize minnE subnn subn0 //.
            assert (Hwbelen1' : 1 < wb_elen1). inversion H0. rewrite Helen in H12. exact H12.
            assert (Hwbmlen1' : 1 < wb_mlen1). inversion H0. rewrite Hmlen in H11. exact H11.
            apply (uelen_ge_elen wb_elen1 wb_mlen1 Hwbelen1' Hwbmlen1').
        specialize (Hcat Hcat_size).
        rewrite -Hcat.
        {
          rewrite to_Z_cat. 
          apply Bool.Is_true_eq_true in He'.
          apply is_ones_ones in He'. rewrite size_low in He'. rewrite He'. unfold max_normal_e. 
          rewrite to_Zpos_ones size_ones.
          rewrite to_Z_from_Z. rewrite Z.add_diag. 
          move : Hminus.
          unfold bias. unfold elen_Z. 
          replace (2 * (2 ^ (Z.of_nat wb_elen1 - 1) - 1))%Z with
            (2 * (2 ^ (Z.of_nat wb_elen1 - 1)) - 2)%Z by lia.
          replace (Z.of_nat wb_elen1 - 1)%Z with (Z.of_nat (wb_elen1 - 1))%Z.
          rewrite -Z.pow_succ_r. rewrite -Nat2Z.inj_succ.
          rewrite subn1 -S_pred_pos.
          replace (2 ^ Z.of_nat wb_elen1 - 2)%Z with (-2 + 2 ^ Z.of_nat wb_elen1)%Z by lia.
          move => Hminus.
          apply Z.lt_sub_lt_add_l. 
          replace (-2 + 2 ^ Z.of_nat wb_elen1 - (2 ^ Z.of_nat wb_elen1 - 1))%Z
            with (-2 + (2 ^ Z.of_nat wb_elen1 - 2 ^ Z.of_nat wb_elen1) + 1)%Z by lia.
          rewrite Z.sub_diag. simpl. 
          replace (-1)%Z with (Z.pred 0) by auto.
          apply Z.lt_pred_le. apply Zmult_gt_0_le_0_compat.
          + apply ZAriths.two_power_of_nat_gt0.
          + exact Hminus.
          + apply Nats.ltn_lt. exact Hwbelen.
          + apply Nat2Z.is_nonneg.
          + replace 1%Z with (Z.of_nat 1)%Z by auto. rewrite Nat2Z.inj_sub //.
          + assert (Hwbelen1' : 1 < wb_elen1). inversion H0. rewrite Helen in H12. exact H12.
          Search (_ < _).
            apply Nats.ltn_lt in Hwbelen1'. apply Nat.lt_le_incl. exact Hwbelen1'.
          + apply uelen_can_represent_bias.
            assert (Hwbelen1' : 1 < wb_elen1). inversion H0. rewrite Helen in H12. exact H12.
            exact Hwbelen1'.
            assert (Hwbmlen1' : 1 < wb_mlen1). inversion H0. rewrite Hmlen in H11. exact H11.
            exact Hwbmlen1'.
          + rewrite size_high.
          + assert (Hwbelen1' : 1 < wb_elen1). inversion H0. rewrite Helen in H12. exact H12.
            assert (Hwbmlen1' : 1 < wb_mlen1). inversion H0. rewrite Hmlen in H11. exact H11.
            move : (uelen_ge_elen wb_elen1 wb_mlen1 Hwbelen1' Hwbmlen1'). move => uelen_ge_elen.
            apply beq_nat_false in Huelen_eq_elen. 
            rewrite subn_gt0.
            apply Nats.leq_le in uelen_ge_elen.
            apply nesym in Huelen_eq_elen.
            apply Nats.lt_ltn. apply Nat.le_neq. split. auto. auto.
        }
        + rewrite -bv2z_add_signed.
          - auto.
          - rewrite size_from_Z //.
          - admit.
          - admit.
          - rewrite size_from_Z. admit.
     }
    }
    rewrite He'. simpl. reflexivity.
  }
  replace (false || false) with false by auto. rewrite is_ones_zeros_false.  
  apply Bool.andb_false_l. apply Hwbelen.
Admitted.

Lemma word_blasting_fp_bexp_semantics_equivalence_isNormal :
  forall (fe : Fq2bvq.fp_exp),
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_exp fe te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1,
            valid_gen_var gen_var ->
              (te1, g1, es1, ubf1, wb_elen1, wb_mlen1) = word_blast_exp gen_var g0 es0 te0 fe ->
                  forall s1 : SSAStore.t,
                    well_formed_bexps es1 te1 && Fq2bvq.well_formed_unpackedbf ubf1 te1 ->
                    conformed_bexps es1 s1 te1 && Fq2bvq.conform_unpackedbf ubf1 s1 te1 ->
                    eval_bexps es1 s1 ->
                      forall pack_s1 pack_e1 pack_m1, 
                        (pack_s1, pack_e1, pack_m1) = pack wb_mlen1 wb_elen1 ubf1 ->
                          forall smt_s1 smt_e1 smt_m1 elen1 mlen1,
                            eval_fp_exp fe s0 (SMTLIBfp.ieee754_fp smt_s1 smt_e1 smt_m1) elen1 mlen1 ->
                            elen1 = wb_elen1 /\
                            mlen1 = wb_mlen1 /\
                            smt_s1 = (QFBV.eval_exp pack_s1 s1) /\ 
                            smt_e1 = (QFBV.eval_exp pack_e1 s1) /\ 
                            smt_m1 = (QFBV.eval_exp pack_m1 s1)) ->
    forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
      Fq2bvq.well_formed_fp_bexp (Fq2bvq.FBunop Fq2bvq.FUisNormal fe) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' b,
              valid_gen_var gen_var ->
                (te', g', es', b) = word_blast_bexp gen_var g es te (Fq2bvq.FBunop Fq2bvq.FUisNormal fe) ->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && QFBV.well_formed_bexp b te' ->
                    conformed_bexps es' s' te' && conform_bexp b s' te' ->
                    eval_bexps es' s' ->
                      forall smt_b, eval_fp_bexp (Fq2bvq.FBunop Fq2bvq.FUisNormal fe) s smt_b ->
                        smt_b = QFBV.eval_bexp b s'.
Proof.
  move => fe IH te s es g /= Hwf Heswf Hescf Hes gen_var g' te' es' b Hgv wb s' Hwbwf Hwbcf Hes' smt_b Hsmt.
  case Hwb: (word_blast_exp gen_var g es te fe) => [[[[[te1 g1] es1] ubf1] wb_elen1] wb_mlen1].
  rewrite Hwb in wb. inversion wb. symmetry in Hwb.
  inversion Hwf.
  specialize (IH te s es g H4 Heswf Hescf Hes gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb).
  move : (word_blasting_fp_exp_is_wellformed fe te es g H4 Heswf gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb) => Hwbwf1.
  move : (word_blasting_fp_exp_is_conformed fe te s es g H4 Heswf Hescf gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb Hwbwf1) => Hwbcf1.
  destruct Hwbcf1 as [s1 Hwbcf1].
  move : (word_blasting_fp_exp_eval_es fe te s es g H4 Heswf Hescf Hes gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb s1 Hwbwf1 Hwbcf1) => Hes1.
  specialize (IH s1 Hwbwf1 Hwbcf1 Hes1).
  case Hpack1: (pack wb_mlen1 wb_elen1 ubf1) => [[pack_s1 pack_e1] pack_m1]. symmetry in Hpack1.
  specialize (IH pack_s1 pack_e1 pack_m1 Hpack1).
  inversion Hsmt. subst. inversion H9. subst.
  specialize (IH s0 e m elen mlen H6). inversion IH.
  assert (Helen : elen = wb_elen1). apply IH.
  assert (Hmlen : mlen = wb_mlen1). apply IH.
  assert (Hs : s0 = QFBV.eval_exp pack_s1 s1). apply IH.
  assert (He : e = QFBV.eval_exp pack_e1 s1). apply IH.
  assert (Hm : m = QFBV.eval_exp pack_m1 s1). apply IH.
  unfold WBClassify.isNormal_unpackedbf. simpl.
  inversion Hpack1. 
  rewrite H5 in He.
  rewrite He. simpl. 
  assert (Hwbelen : wb_elen1 > 0). 
  + inversion H0. rewrite -Helen. auto.
  assert (Hwbmlen : wb_mlen1 > 0).
  + inversion H0. rewrite -Hmlen. auto.
  assert (is_ones_zeros_false : forall n, n > 0 -> is_ones (zeros n) = false).
  + destruct n. auto. auto.
  assert (is_zero_ones_false : forall n, n > 0 -> is_zero (ones n) = false). 
  + destruct n. auto. auto.
  assert (Hnan_flag' : QFBV.eval_bexp (nan_flag ubf1) s' = QFBV.eval_bexp (nan_flag ubf1) s1). admit.
  assert (Hzero_flag' : QFBV.eval_bexp (zero_flag ubf1) s' = QFBV.eval_bexp (zero_flag ubf1) s1). admit.
  assert (Hinf_flag' : QFBV.eval_bexp (inf_flag ubf1) s' = QFBV.eval_bexp (inf_flag ubf1) s1). admit.
  assert (Hun_e' : QFBV.eval_exp (un_e ubf1) s' = QFBV.eval_exp (un_e ubf1) s1). admit.
  rewrite Hnan_flag' Hzero_flag' Hinf_flag' Hun_e'. 
  case Hnan : (QFBV.eval_bexp (nan_flag ubf1) s1). simpl.
  rewrite ones_is_ones. simpl. rewrite Bool.andb_false_r. rewrite Bool.andb_false_l. auto.
  case Hinf : (QFBV.eval_bexp (inf_flag ubf1) s1). simpl.
  rewrite ones_is_ones //. 
  case Hzero : (QFBV.eval_bexp (zero_flag ubf1) s1). simpl.
  rewrite zeros_is_zero. simpl. rewrite Bool.andb_false_r //.
  case Hnormal :      
    (sleB
       (sext
          (unpack_elen wb_mlen1 wb_elen1 -
           unpack_elen wb_mlen1 wb_elen1)
          (unpack_elen wb_mlen1 wb_elen1) -bits
          of Z (min_normal_e wb_elen1)%bits)
       (QFBV.eval_exp (un_e ubf1) s1) &&
     sleB (QFBV.eval_exp (un_e ubf1) s1)
       (sext
          (unpack_elen wb_mlen1 wb_elen1 -
           unpack_elen wb_mlen1 wb_elen1)
          (unpack_elen wb_mlen1 wb_elen1) -bits
          of Z (max_normal_e wb_elen1)%bits)). replace (false || false) with false by auto. 
  {
      simpl. rewrite -negb_or. apply Bool.negb_true_iff. apply Bool.orb_false_intro.
      admit. (* copy proof of isNaN *)
      admit. (* copy proof of isZero *)
  }
  rewrite is_ones_zeros_false. rewrite zeros_is_zero //.
Admitted.

Lemma word_blasting_fp_bexp_semantics_equivalence_isSubNormal :
  forall (fe : Fq2bvq.fp_exp),
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_exp fe te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1,
            valid_gen_var gen_var ->
              (te1, g1, es1, ubf1, wb_elen1, wb_mlen1) = word_blast_exp gen_var g0 es0 te0 fe ->
                  forall s1 : SSAStore.t,
                    well_formed_bexps es1 te1 && Fq2bvq.well_formed_unpackedbf ubf1 te1 ->
                    conformed_bexps es1 s1 te1 && Fq2bvq.conform_unpackedbf ubf1 s1 te1 ->
                    eval_bexps es1 s1 ->
                      forall pack_s1 pack_e1 pack_m1, 
                        (pack_s1, pack_e1, pack_m1) = pack wb_mlen1 wb_elen1 ubf1 ->
                          forall smt_s1 smt_e1 smt_m1 elen1 mlen1,
                            eval_fp_exp fe s0 (SMTLIBfp.ieee754_fp smt_s1 smt_e1 smt_m1) elen1 mlen1 ->
                            elen1 = wb_elen1 /\
                            mlen1 = wb_mlen1 /\
                            smt_s1 = (QFBV.eval_exp pack_s1 s1) /\ 
                            smt_e1 = (QFBV.eval_exp pack_e1 s1) /\ 
                            smt_m1 = (QFBV.eval_exp pack_m1 s1)) ->
    forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
      Fq2bvq.well_formed_fp_bexp (Fq2bvq.FBunop Fq2bvq.FUisSubnormal fe) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' b,
              valid_gen_var gen_var ->
                (te', g', es', b) = word_blast_bexp gen_var g es te (Fq2bvq.FBunop Fq2bvq.FUisSubnormal fe) ->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && QFBV.well_formed_bexp b te' ->
                    conformed_bexps es' s' te' && conform_bexp b s' te' ->
                    eval_bexps es' s' ->
                      forall smt_b, eval_fp_bexp (Fq2bvq.FBunop Fq2bvq.FUisSubnormal fe) s smt_b ->
                        smt_b = QFBV.eval_bexp b s'.
Proof.
  move => fe IH te s es g /= Hwf Heswf Hescf Hes gen_var g' te' es' b Hgv wb s' Hwbwf Hwbcf Hes' smt_b Hsmt.
  case Hwb: (word_blast_exp gen_var g es te fe) => [[[[[te1 g1] es1] ubf1] wb_elen1] wb_mlen1].
  rewrite Hwb in wb. inversion wb. symmetry in Hwb.
  inversion Hwf.
  specialize (IH te s es g H4 Heswf Hescf Hes gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb).
  move : (word_blasting_fp_exp_is_wellformed fe te es g H4 Heswf gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb) => Hwbwf1.
  move : (word_blasting_fp_exp_is_conformed fe te s es g H4 Heswf Hescf gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb Hwbwf1) => Hwbcf1.
  destruct Hwbcf1 as [s1 Hwbcf1].
  move : (word_blasting_fp_exp_eval_es fe te s es g H4 Heswf Hescf Hes gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb s1 Hwbwf1 Hwbcf1) => Hes1.
  specialize (IH s1 Hwbwf1 Hwbcf1 Hes1).
  case Hpack1: (pack wb_mlen1 wb_elen1 ubf1) => [[pack_s1 pack_e1] pack_m1]. symmetry in Hpack1.
  specialize (IH pack_s1 pack_e1 pack_m1 Hpack1).
  inversion Hsmt. subst. inversion H9. subst.
  specialize (IH s0 e m elen mlen H6). inversion IH.
  assert (Helen : elen = wb_elen1). apply IH.
  assert (Hmlen : mlen = wb_mlen1). apply IH.
  assert (Hs : s0 = QFBV.eval_exp pack_s1 s1). apply IH.
  assert (He : e = QFBV.eval_exp pack_e1 s1). apply IH.
  assert (Hm : m = QFBV.eval_exp pack_m1 s1). apply IH.
  unfold WBClassify.isSubNormal_unpackedbf. simpl.
  inversion Hpack1. 
  rewrite H5 in He. rewrite H7 in Hm.
  rewrite He Hm. simpl. 
  assert (Hwbelen : wb_elen1 > 0). 
  + inversion H0. rewrite -Helen. auto.
  assert (Hwbmlen : wb_mlen1 > 0).
  + inversion H0. rewrite -Hmlen. auto.
  assert (is_ones_zeros_false : forall n, n > 0 -> is_ones (zeros n) = false).
  + destruct n. auto. auto.
  assert (is_zero_ones_false : forall n, n > 0 -> is_zero (ones n) = false). 
  + destruct n. auto. auto.
  assert (Hnan_flag' : QFBV.eval_bexp (nan_flag ubf1) s' = QFBV.eval_bexp (nan_flag ubf1) s1). admit.
  assert (Hzero_flag' : QFBV.eval_bexp (zero_flag ubf1) s' = QFBV.eval_bexp (zero_flag ubf1) s1). admit.
  assert (Hinf_flag' : QFBV.eval_bexp (inf_flag ubf1) s' = QFBV.eval_bexp (inf_flag ubf1) s1). admit.
  assert (Hun_e' : QFBV.eval_exp (un_e ubf1) s' = QFBV.eval_exp (un_e ubf1) s1). admit.
  rewrite Hnan_flag' Hzero_flag' Hinf_flag' Hun_e'. 
  case Hnan : (QFBV.eval_bexp (nan_flag ubf1) s1). simpl.
  rewrite is_zero_ones_false. simpl. rewrite Bool.andb_false_r. rewrite Bool.andb_false_l. auto.
  exact Hwbelen.
  case Hinf : (QFBV.eval_bexp (inf_flag ubf1) s1). simpl.
  rewrite is_zero_ones_false //. 
  case Hzero : (QFBV.eval_bexp (zero_flag ubf1) s1). simpl.
  rewrite zeros_is_zero zeros_is_zero //. 
  case Hnormal :      
    (sleB
       (sext
          (unpack_elen wb_mlen1 wb_elen1 -
           unpack_elen wb_mlen1 wb_elen1)
          (unpack_elen wb_mlen1 wb_elen1) -bits
          of Z (min_normal_e wb_elen1)%bits)
       (QFBV.eval_exp (un_e ubf1) s1) &&
     sleB (QFBV.eval_exp (un_e ubf1) s1)
       (sext
          (unpack_elen wb_mlen1 wb_elen1 -
           unpack_elen wb_mlen1 wb_elen1)
          (unpack_elen wb_mlen1 wb_elen1) -bits
          of Z (max_normal_e wb_elen1)%bits)). replace (false || false) with false by auto. 
  {
      simpl. 
      assert (Hsubnormal : sleB
                (sext (unpack_elen wb_mlen1 wb_elen1 - unpack_elen wb_mlen1 wb_elen1)
                   (unpack_elen wb_mlen1 wb_elen1) -bits
                   of Z (min_subnormal_e wb_mlen1 wb_elen1)%bits)
                (QFBV.eval_exp (un_e ubf1) s1) &&
              sleB (QFBV.eval_exp (un_e ubf1) s1)
                (sext (unpack_elen wb_mlen1 wb_elen1 - unpack_elen wb_mlen1 wb_elen1)
                   (unpack_elen wb_mlen1 wb_elen1) -bits of Z (max_subnormal_e wb_elen1)%bits) = false).
      {
        admit. (* proof by Hnormal *)
      }
      rewrite Hsubnormal.
      assert (He' : (is_zero
                      (low wb_elen1
                         (QFBV.eval_exp (un_e ubf1) s1 +#
                          (unpack_elen wb_mlen1 wb_elen1) -bits
                          of Z (bias wb_elen1))%bits) = false)).
      {
        admit. (* copy proof of isZero *)
      }
      rewrite He' //.
  }
  rewrite zeros_is_zero. simpl.
  assert (Hsubnormal : sleB
            (sext (unpack_elen wb_mlen1 wb_elen1 - unpack_elen wb_mlen1 wb_elen1)
               (unpack_elen wb_mlen1 wb_elen1) -bits
               of Z (min_subnormal_e wb_mlen1 wb_elen1)%bits)
            (QFBV.eval_exp (un_e ubf1) s1) &&
          sleB (QFBV.eval_exp (un_e ubf1) s1)
            (sext (unpack_elen wb_mlen1 wb_elen1 - unpack_elen wb_mlen1 wb_elen1)
               (unpack_elen wb_mlen1 wb_elen1) -bits of Z (max_subnormal_e wb_elen1)%bits) = true).
  {
    admit. (* similar proof of Hsubnormal *)
  }
  rewrite Hsubnormal.
  admit. (* copy proof of subnormal case of isZero *)
Admitted.

Lemma word_blasting_fp_bexp_semantics_equivalence_isNegative :
  forall (fe : Fq2bvq.fp_exp),
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_exp fe te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1,
            valid_gen_var gen_var ->
              (te1, g1, es1, ubf1, wb_elen1, wb_mlen1) = word_blast_exp gen_var g0 es0 te0 fe ->
                  forall s1 : SSAStore.t,
                    well_formed_bexps es1 te1 && Fq2bvq.well_formed_unpackedbf ubf1 te1 ->
                    conformed_bexps es1 s1 te1 && Fq2bvq.conform_unpackedbf ubf1 s1 te1 ->
                    eval_bexps es1 s1 ->
                      forall pack_s1 pack_e1 pack_m1, 
                        (pack_s1, pack_e1, pack_m1) = pack wb_mlen1 wb_elen1 ubf1 ->
                          forall smt_s1 smt_e1 smt_m1 elen1 mlen1,
                            eval_fp_exp fe s0 (SMTLIBfp.ieee754_fp smt_s1 smt_e1 smt_m1) elen1 mlen1 ->
                            elen1 = wb_elen1 /\
                            mlen1 = wb_mlen1 /\
                            smt_s1 = (QFBV.eval_exp pack_s1 s1) /\ 
                            smt_e1 = (QFBV.eval_exp pack_e1 s1) /\ 
                            smt_m1 = (QFBV.eval_exp pack_m1 s1)) ->
    forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
      Fq2bvq.well_formed_fp_bexp (Fq2bvq.FBunop Fq2bvq.FUisNegative fe) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' b,
              valid_gen_var gen_var ->
                (te', g', es', b) = word_blast_bexp gen_var g es te (Fq2bvq.FBunop Fq2bvq.FUisNegative fe) ->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && QFBV.well_formed_bexp b te' ->
                    conformed_bexps es' s' te' && conform_bexp b s' te' ->
                    eval_bexps es' s' ->
                      forall smt_b, eval_fp_bexp (Fq2bvq.FBunop Fq2bvq.FUisNegative fe) s smt_b ->
                        smt_b = QFBV.eval_bexp b s'.
Proof.
  move => fe IH te s es g /= Hwf Heswf Hescf Hes gen_var g' te' es' b Hgv wb s' Hwbwf Hwbcf Hes' smt_b Hsmt.
  case Hwb: (word_blast_exp gen_var g es te fe) => [[[[[te1 g1] es1] ubf1] wb_elen1] wb_mlen1].
  rewrite Hwb in wb. inversion wb. symmetry in Hwb.
  inversion Hwf.
  specialize (IH te s es g H4 Heswf Hescf Hes gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb).
  move : (word_blasting_fp_exp_is_wellformed fe te es g H4 Heswf gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb) => Hwbwf1.
  move : (word_blasting_fp_exp_is_conformed fe te s es g H4 Heswf Hescf gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb Hwbwf1) => Hwbcf1.
  destruct Hwbcf1 as [s1 Hwbcf1].
  move : (word_blasting_fp_exp_eval_es fe te s es g H4 Heswf Hescf Hes gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb s1 Hwbwf1 Hwbcf1) => Hes1.
  specialize (IH s1 Hwbwf1 Hwbcf1 Hes1).
  case Hpack1: (pack wb_mlen1 wb_elen1 ubf1) => [[pack_s1 pack_e1] pack_m1]. symmetry in Hpack1.
  specialize (IH pack_s1 pack_e1 pack_m1 Hpack1).
  inversion Hsmt. subst. inversion H9. subst. inversion H. subst.
  specialize (IH s0 e m elen mlen H6). inversion IH.
  assert (Helen : elen = wb_elen1). apply IH.
  assert (Hmlen : mlen = wb_mlen1). apply IH.
  assert (Hs : s0 = QFBV.eval_exp pack_s1 s1). apply IH.
  assert (He : e = QFBV.eval_exp pack_e1 s1). apply IH.
  assert (Hm : m = QFBV.eval_exp pack_m1 s1). apply IH.
  unfold WBClassify.isInfinite_unpackedbf. simpl.
  inversion Hpack1. 
  rewrite H7 in He. rewrite H10 in Hm. 
  rewrite He Hm. simpl. 
  assert (Hwbelen : wb_elen1 > 0). 
  + inversion H1. rewrite -Helen. auto.
  assert (Hwbmlen : wb_mlen1 > 0).
  + inversion H1. rewrite -Hmlen. auto.
  assert (is_ones_zeros_false : forall n, n > 0 -> is_ones (zeros n) = false).
  + destruct n. auto. auto.
  assert (is_zero_ones_false : forall n, n > 0 -> is_zero (ones n) = false). 
  + destruct n. auto. auto.
  assert (Hnan_flag' : QFBV.eval_bexp (nan_flag ubf1) s' = QFBV.eval_bexp (nan_flag ubf1) s1). admit.
  assert (Hun_s' : QFBV.eval_bexp (un_s ubf1) s' = QFBV.eval_bexp (un_s ubf1) s1). admit.
  rewrite Hnan_flag' Hun_s'. case Hnan : (QFBV.eval_bexp (nan_flag ubf1) s1). simpl.
  rewrite ones_is_ones is_zero_ones_false. auto.
  apply Hwbmlen. 
  case Hinf : (QFBV.eval_bexp (inf_flag ubf1) s1). simpl.
  rewrite ones_is_ones. rewrite zeros_is_zero. simpl.
  rewrite Hs H5. simpl. rewrite Hnan.
  destruct (QFBV.eval_bexp (un_s ubf1) s1). auto. auto.
  case Hzero : (QFBV.eval_bexp (zero_flag ubf1) s1). simpl.
  rewrite is_ones_zeros_false. rewrite zeros_is_zero. simpl.
  rewrite Hs H5. simpl. rewrite Hnan.
  destruct (QFBV.eval_bexp (un_s ubf1) s1). auto. auto.
  apply Hwbelen.
  case Hnormal :      
    (sleB
       (sext
          (unpack_elen wb_mlen1 wb_elen1 -
           unpack_elen wb_mlen1 wb_elen1)
          (unpack_elen wb_mlen1 wb_elen1) -bits
          of Z (min_normal_e wb_elen1)%bits)
       (QFBV.eval_exp (un_e ubf1) s1) &&
     sleB (QFBV.eval_exp (un_e ubf1) s1)
       (sext
          (unpack_elen wb_mlen1 wb_elen1 -
           unpack_elen wb_mlen1 wb_elen1)
          (unpack_elen wb_mlen1 wb_elen1) -bits
          of Z (max_normal_e wb_elen1)%bits)). replace (false || false) with false by auto.
  {
     
     assert (He' : (is_ones
                    (low wb_elen1
                       (QFBV.eval_exp (un_e ubf1) s1 +#
                        (unpack_elen wb_mlen1 wb_elen1) -bits
                        of Z (bias wb_elen1))%bits) = false)). admit. (* copy proof of isNaN *) 
     rewrite He'. simpl.
     rewrite Hs H5. simpl. rewrite Hnan.
     destruct (QFBV.eval_bexp (un_s ubf1) s1). auto. auto.
  }
  replace (false || false) with false by auto.
  rewrite is_ones_zeros_false. simpl.
  rewrite Hs H5. simpl. rewrite Hnan.
  destruct (QFBV.eval_bexp (un_s ubf1) s1). auto. auto.
  apply Hwbelen.
Admitted.

Lemma word_blasting_fp_bexp_semantics_equivalence_isPositive :
  forall (fe : Fq2bvq.fp_exp),
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_exp fe te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1,
            valid_gen_var gen_var ->
              (te1, g1, es1, ubf1, wb_elen1, wb_mlen1) = word_blast_exp gen_var g0 es0 te0 fe ->
                  forall s1 : SSAStore.t,
                    well_formed_bexps es1 te1 && Fq2bvq.well_formed_unpackedbf ubf1 te1 ->
                    conformed_bexps es1 s1 te1 && Fq2bvq.conform_unpackedbf ubf1 s1 te1 ->
                    eval_bexps es1 s1 ->
                      forall pack_s1 pack_e1 pack_m1, 
                        (pack_s1, pack_e1, pack_m1) = pack wb_mlen1 wb_elen1 ubf1 ->
                          forall smt_s1 smt_e1 smt_m1 elen1 mlen1,
                            eval_fp_exp fe s0 (SMTLIBfp.ieee754_fp smt_s1 smt_e1 smt_m1) elen1 mlen1 ->
                            elen1 = wb_elen1 /\
                            mlen1 = wb_mlen1 /\
                            smt_s1 = (QFBV.eval_exp pack_s1 s1) /\ 
                            smt_e1 = (QFBV.eval_exp pack_e1 s1) /\ 
                            smt_m1 = (QFBV.eval_exp pack_m1 s1)) ->
    forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
      Fq2bvq.well_formed_fp_bexp (Fq2bvq.FBunop Fq2bvq.FUisPositive fe) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' b,
              valid_gen_var gen_var ->
                (te', g', es', b) = word_blast_bexp gen_var g es te (Fq2bvq.FBunop Fq2bvq.FUisPositive fe) ->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && QFBV.well_formed_bexp b te' ->
                    conformed_bexps es' s' te' && conform_bexp b s' te' ->
                    eval_bexps es' s' ->
                      forall smt_b, eval_fp_bexp (Fq2bvq.FBunop Fq2bvq.FUisPositive fe) s smt_b ->
                        smt_b = QFBV.eval_bexp b s'.
Proof.
  move => fe IH te s es g /= Hwf Heswf Hescf Hes gen_var g' te' es' b Hgv wb s' Hwbwf Hwbcf Hes' smt_b Hsmt.
  case Hwb: (word_blast_exp gen_var g es te fe) => [[[[[te1 g1] es1] ubf1] wb_elen1] wb_mlen1].
  rewrite Hwb in wb. inversion wb. symmetry in Hwb.
  inversion Hwf.
  specialize (IH te s es g H4 Heswf Hescf Hes gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb).
  move : (word_blasting_fp_exp_is_wellformed fe te es g H4 Heswf gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb) => Hwbwf1.
  move : (word_blasting_fp_exp_is_conformed fe te s es g H4 Heswf Hescf gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb Hwbwf1) => Hwbcf1.
  destruct Hwbcf1 as [s1 Hwbcf1].
  move : (word_blasting_fp_exp_eval_es fe te s es g H4 Heswf Hescf Hes gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb s1 Hwbwf1 Hwbcf1) => Hes1.
  specialize (IH s1 Hwbwf1 Hwbcf1 Hes1).
  case Hpack1: (pack wb_mlen1 wb_elen1 ubf1) => [[pack_s1 pack_e1] pack_m1]. symmetry in Hpack1.
  specialize (IH pack_s1 pack_e1 pack_m1 Hpack1).
  inversion Hsmt. subst. inversion H9. subst. inversion H. subst.
  specialize (IH s0 e m elen mlen H6). inversion IH.
  assert (Helen : elen = wb_elen1). apply IH.
  assert (Hmlen : mlen = wb_mlen1). apply IH.
  assert (Hs : s0 = QFBV.eval_exp pack_s1 s1). apply IH.
  assert (He : e = QFBV.eval_exp pack_e1 s1). apply IH.
  assert (Hm : m = QFBV.eval_exp pack_m1 s1). apply IH.
  unfold WBClassify.isInfinite_unpackedbf. simpl.
  inversion Hpack1. 
  rewrite H7 in He. rewrite H10 in Hm. 
  rewrite He Hm. simpl. 
  assert (Hwbelen : wb_elen1 > 0). 
  + inversion H1. rewrite -Helen. auto.
  assert (Hwbmlen : wb_mlen1 > 0).
  + inversion H1. rewrite -Hmlen. auto.
  assert (is_ones_zeros_false : forall n, n > 0 -> is_ones (zeros n) = false).
  + destruct n. auto. auto.
  assert (is_zero_ones_false : forall n, n > 0 -> is_zero (ones n) = false). 
  + destruct n. auto. auto.
  assert (Hnan_flag' : QFBV.eval_bexp (nan_flag ubf1) s' = QFBV.eval_bexp (nan_flag ubf1) s1). admit.
  assert (Hun_s' : QFBV.eval_bexp (un_s ubf1) s' = QFBV.eval_bexp (un_s ubf1) s1). admit.
  rewrite Hnan_flag' Hun_s'. case Hnan : (QFBV.eval_bexp (nan_flag ubf1) s1). simpl.
  rewrite ones_is_ones is_zero_ones_false. auto.
  apply Hwbmlen. 
  case Hinf : (QFBV.eval_bexp (inf_flag ubf1) s1). simpl.
  rewrite ones_is_ones. rewrite zeros_is_zero. simpl.
  rewrite Hs H5. simpl. rewrite Hnan.
  destruct (QFBV.eval_bexp (un_s ubf1) s1). auto. auto.
  case Hzero : (QFBV.eval_bexp (zero_flag ubf1) s1). simpl.
  rewrite is_ones_zeros_false. rewrite zeros_is_zero. simpl.
  rewrite Hs H5. simpl. rewrite Hnan.
  destruct (QFBV.eval_bexp (un_s ubf1) s1). auto. auto.
  apply Hwbelen.
  case Hnormal :      
    (sleB
       (sext
          (unpack_elen wb_mlen1 wb_elen1 -
           unpack_elen wb_mlen1 wb_elen1)
          (unpack_elen wb_mlen1 wb_elen1) -bits
          of Z (min_normal_e wb_elen1)%bits)
       (QFBV.eval_exp (un_e ubf1) s1) &&
     sleB (QFBV.eval_exp (un_e ubf1) s1)
       (sext
          (unpack_elen wb_mlen1 wb_elen1 -
           unpack_elen wb_mlen1 wb_elen1)
          (unpack_elen wb_mlen1 wb_elen1) -bits
          of Z (max_normal_e wb_elen1)%bits)). replace (false || false) with false by auto.
  {
     
     assert (He' : (is_ones
                    (low wb_elen1
                       (QFBV.eval_exp (un_e ubf1) s1 +#
                        (unpack_elen wb_mlen1 wb_elen1) -bits
                        of Z (bias wb_elen1))%bits) = false)). admit. (* copy proof of isNaN *) 
     rewrite He'. simpl.
     rewrite Hs H5. simpl. rewrite Hnan.
     destruct (QFBV.eval_bexp (un_s ubf1) s1). auto. auto.
  }
  replace (false || false) with false by auto.
  rewrite is_ones_zeros_false. simpl.
  rewrite Hs H5. simpl. rewrite Hnan.
  destruct (QFBV.eval_bexp (un_s ubf1) s1). auto. auto.
  apply Hwbelen.
Admitted.



Lemma word_blasting_fp_bexp_semantics_equivalence_unop :
  forall (op : Fq2bvq.fbunop) (fe : Fq2bvq.fp_exp),
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_exp fe te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1,
            valid_gen_var gen_var ->
              (te1, g1, es1, ubf1, wb_elen1, wb_mlen1) = word_blast_exp gen_var g0 es0 te0 fe ->
                  forall s1 : SSAStore.t,
                    well_formed_bexps es1 te1 && Fq2bvq.well_formed_unpackedbf ubf1 te1 ->
                    conformed_bexps es1 s1 te1 && Fq2bvq.conform_unpackedbf ubf1 s1 te1 ->
                    eval_bexps es1 s1 ->
                      forall pack_s1 pack_e1 pack_m1, 
                        (pack_s1, pack_e1, pack_m1) = pack wb_mlen1 wb_elen1 ubf1 ->
                          forall smt_s1 smt_e1 smt_m1 elen1 mlen1,
                            eval_fp_exp fe s0 (SMTLIBfp.ieee754_fp smt_s1 smt_e1 smt_m1) elen1 mlen1 ->
                            elen1 = wb_elen1 /\
                            mlen1 = wb_mlen1 /\
                            smt_s1 = (QFBV.eval_exp pack_s1 s1) /\ 
                            smt_e1 = (QFBV.eval_exp pack_e1 s1) /\ 
                            smt_m1 = (QFBV.eval_exp pack_m1 s1)) ->
    forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
      Fq2bvq.well_formed_fp_bexp (Fq2bvq.FBunop op fe) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' b,
              valid_gen_var gen_var ->
                (te', g', es', b) = word_blast_bexp gen_var g es te (Fq2bvq.FBunop op fe) ->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && QFBV.well_formed_bexp b te' ->
                    conformed_bexps es' s' te' && conform_bexp b s' te' ->
                    eval_bexps es' s' ->
                      forall smt_b, eval_fp_bexp (Fq2bvq.FBunop op fe) s smt_b ->
                        smt_b = QFBV.eval_bexp b s'.
Proof.
Admitted.

End BUnop.


Section BBinop.

Lemma word_blasting_fp_bexp_semantics_equivalence_eq :
  forall fe1 fe2: Fq2bvq.fp_exp,
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_exp fe1 te0 ->
      Fq2bvq.well_formed_fp_exp fe2 te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1,
            valid_gen_var gen_var ->
              (te1, g1, es1, ubf1, wb_elen1, wb_mlen1) = word_blast_exp gen_var g0 es0 te0 fe1 ->
                forall s1 : SSAStore.t,
                  well_formed_bexps es1 te1 && Fq2bvq.well_formed_unpackedbf ubf1 te1 ->
                  conformed_bexps es1 s1 te1 && Fq2bvq.conform_unpackedbf ubf1 s1 te1 ->
                  eval_bexps es1 s1 ->
                    forall pack_s1 pack_e1 pack_m1, 
                      (pack_s1, pack_e1, pack_m1) = pack wb_mlen1 wb_elen1 ubf1 ->
                        forall smt_s1 smt_e1 smt_m1 elen1 mlen1,
                          eval_fp_exp fe1 s0 (SMTLIBfp.ieee754_fp smt_s1 smt_e1 smt_m1) elen1 mlen1 ->
          forall g2 te2 es2 ubf2 wb_elen2 wb_mlen2,
              (te2, g2, es2, ubf2, wb_elen2, wb_mlen2) = word_blast_exp gen_var g1 es1 te1 fe2 ->
                forall s2 : SSAStore.t,
                  well_formed_bexps es2 te2 && Fq2bvq.well_formed_unpackedbf ubf2 te2 ->
                  conformed_bexps es2 s2 te2 && Fq2bvq.conform_unpackedbf ubf2 s2 te2 ->
                  eval_bexps es2 s2 ->
                    forall pack_s2 pack_e2 pack_m2, 
                      (pack_s2, pack_e2, pack_m2) = pack wb_mlen2 wb_elen2 ubf2 ->
                        forall smt_s2 smt_e2 smt_m2 elen2 mlen2,
                          eval_fp_exp fe2 s0 (SMTLIBfp.ieee754_fp smt_s2 smt_e2 smt_m2) elen2 mlen2 ->
                            (elen1 = wb_elen1 /\
                            mlen1 = wb_mlen1 /\
                            smt_s1 = (QFBV.eval_exp pack_s1 s1) /\ 
                            smt_e1 = (QFBV.eval_exp pack_e1 s1) /\ 
                            smt_m1 = (QFBV.eval_exp pack_m1 s1)) /\ 
                            (elen2 = wb_elen2 /\
                            mlen2 = wb_mlen2 /\
                            smt_s2 = (QFBV.eval_exp pack_s2 s2) /\ 
                            smt_e2 = (QFBV.eval_exp pack_e2 s2) /\ 
                            smt_m2 = (QFBV.eval_exp pack_m2 s2))) -> 
    forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
      Fq2bvq.well_formed_fp_bexp (Fq2bvq.FBbinop Fq2bvq.FBeq fe1 fe2) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' b,
              valid_gen_var gen_var ->
                (te', g', es', b) = word_blast_bexp gen_var g es te (Fq2bvq.FBbinop Fq2bvq.FBeq fe1 fe2) ->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && QFBV.well_formed_bexp b te' ->
                    conformed_bexps es' s' te' && conform_bexp b s' te' ->
                    eval_bexps es' s' ->
                      forall smt_b, eval_fp_bexp (Fq2bvq.FBbinop Fq2bvq.FBeq fe1 fe2) s smt_b ->
                        smt_b = QFBV.eval_bexp b s'.
Proof.
Admitted. 

Lemma word_blasting_fp_bexp_semantics_equivalence_lt :
  forall fe1 fe2: Fq2bvq.fp_exp,
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_exp fe1 te0 ->
      Fq2bvq.well_formed_fp_exp fe2 te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1,
            valid_gen_var gen_var ->
              (te1, g1, es1, ubf1, wb_elen1, wb_mlen1) = word_blast_exp gen_var g0 es0 te0 fe1 ->
                forall s1 : SSAStore.t,
                  well_formed_bexps es1 te1 && Fq2bvq.well_formed_unpackedbf ubf1 te1 ->
                  conformed_bexps es1 s1 te1 && Fq2bvq.conform_unpackedbf ubf1 s1 te1 ->
                  eval_bexps es1 s1 ->
                    forall pack_s1 pack_e1 pack_m1, 
                      (pack_s1, pack_e1, pack_m1) = pack wb_mlen1 wb_elen1 ubf1 ->
                        forall smt_s1 smt_e1 smt_m1 elen1 mlen1,
                          eval_fp_exp fe1 s0 (SMTLIBfp.ieee754_fp smt_s1 smt_e1 smt_m1) elen1 mlen1 ->
          forall g2 te2 es2 ubf2 wb_elen2 wb_mlen2,
              (te2, g2, es2, ubf2, wb_elen2, wb_mlen2) = word_blast_exp gen_var g1 es1 te1 fe2 ->
                forall s2 : SSAStore.t,
                  well_formed_bexps es2 te2 && Fq2bvq.well_formed_unpackedbf ubf2 te2 ->
                  conformed_bexps es2 s2 te2 && Fq2bvq.conform_unpackedbf ubf2 s2 te2 ->
                  eval_bexps es2 s2 ->
                    forall pack_s2 pack_e2 pack_m2, 
                      (pack_s2, pack_e2, pack_m2) = pack wb_mlen2 wb_elen2 ubf2 ->
                        forall smt_s2 smt_e2 smt_m2 elen2 mlen2,
                          eval_fp_exp fe2 s0 (SMTLIBfp.ieee754_fp smt_s2 smt_e2 smt_m2) elen2 mlen2 ->
                            (elen1 = wb_elen1 /\
                            mlen1 = wb_mlen1 /\
                            smt_s1 = (QFBV.eval_exp pack_s1 s1) /\ 
                            smt_e1 = (QFBV.eval_exp pack_e1 s1) /\ 
                            smt_m1 = (QFBV.eval_exp pack_m1 s1)) /\ 
                            (elen2 = wb_elen2 /\
                            mlen2 = wb_mlen2 /\
                            smt_s2 = (QFBV.eval_exp pack_s2 s2) /\ 
                            smt_e2 = (QFBV.eval_exp pack_e2 s2) /\ 
                            smt_m2 = (QFBV.eval_exp pack_m2 s2))) -> 
    forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
      Fq2bvq.well_formed_fp_bexp (Fq2bvq.FBbinop Fq2bvq.FBlt fe1 fe2) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' b,
              valid_gen_var gen_var ->
                (te', g', es', b) = word_blast_bexp gen_var g es te (Fq2bvq.FBbinop Fq2bvq.FBlt fe1 fe2) ->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && QFBV.well_formed_bexp b te' ->
                    conformed_bexps es' s' te' && conform_bexp b s' te' ->
                    eval_bexps es' s' ->
                      forall smt_b, eval_fp_bexp (Fq2bvq.FBbinop Fq2bvq.FBlt fe1 fe2) s smt_b ->
                        smt_b = QFBV.eval_bexp b s'.
Proof.
  move => fe1 fe2 IH /= te s es g Hwf Heswf Hescf Hes gen_var g' te' es' b Hgv wb s' Hwbwf Hwbcf Hes' smt_b Hsmt.
  case Hwb1: (word_blast_exp gen_var g es te fe1) => [[[[[te1 g1] es1] ubf1] wb_elen1] wb_mlen1].
  case Hwb2: (word_blast_exp gen_var g1 es1 te1 fe2) => [[[[[te2 g2] es2] ubf2] wb_elen2] wb_mlen2].
  rewrite Hwb1 Hwb2 in wb. inversion wb. symmetry in Hwb1. symmetry in Hwb2. 
  case Hfef1 : (Fq2bvq.fp_exp_format fe1) => [fe_elen1 fe_mlen1].
  case Hfef2 : (Fq2bvq.fp_exp_format fe2) => [fe_elen2 fe_mlen2].
  rewrite Hfef1 Hfef2 in Hwf.
  move : Hwf => /andP [/andP [/andP [/andP [/andP [/andP [Hwf1 Hwf2] Hfe_elen1] Hfe_mlen1] Hfe_elen1_le_mlen1] Hfe_elen_eq] Hfe_mlen_eq].
  move : (word_blasting_fp_exp_is_wellformed fe1 te es g Hwf1 Heswf gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb1) => Hwbwf1.
  move : (word_blasting_fp_exp_is_conformed fe1 te s es g Hwf1 Heswf Hescf gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb1 Hwbwf1) => Hwbcf1.
  destruct Hwbcf1 as [s1 Hwbcf1].
  move : (word_blasting_fp_exp_eval_es fe1 te s es g Hwf1 Heswf Hescf Hes gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb1 s1 Hwbwf1 Hwbcf1) => Hes1.
  specialize (IH te s es g Hwf1 Hwf2 Heswf Hescf Hes gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb1 s1 Hwbwf1 Hwbcf1 Hes1).
  case Hpack1: (pack wb_mlen1 wb_elen1 ubf1) => [[pack_s1 pack_e1] pack_m1]. symmetry in Hpack1.
  specialize (IH pack_s1 pack_e1 pack_m1 Hpack1).
  
  assert (Hwf2' : Fq2bvq.well_formed_fp_exp fe2 te1). admit.
  move : Hwbwf1 => Hwbwf1'.
  assert (Hwbwf1 : well_formed_bexps es1 te1 && Fq2bvq.well_formed_unpackedbf ubf1 te1). auto.
  apply Bools.and_true in Hwbwf1'. move : Hwbwf1' => [Heswf1 Hbwf1].
  move : (word_blasting_fp_exp_is_wellformed fe2 te1 es1 g1 Hwf2' Heswf1 gen_var g2 te2 es2 ubf2 wb_elen2 wb_mlen2 Hgv Hwb2) => Hwbwf2.
  move : Hwbcf1 => Hwbcf1'.
  assert (Hwbcf1 : conformed_bexps es1 s1 te1 && Fq2bvq.conform_unpackedbf ubf1 s1 te1). auto.
  apply Bools.and_true in Hwbcf1'. move : Hwbcf1' => [Hescf1 Hbcf1].
  move : (word_blasting_fp_exp_is_conformed fe2 te1 s1 es1 g1 Hwf2' Heswf1 Hescf1 gen_var g2 te2 es2 ubf2 wb_elen2 wb_mlen2 Hgv Hwb2 Hwbwf2) => Hwbcf2.
  destruct Hwbcf2 as [s2 Hwbcf2].
  move : (word_blasting_fp_exp_eval_es fe2 te1 s1 es1 g1 Hwf2' Heswf1 Hescf1 Hes1 gen_var g2 te2 es2 ubf2 wb_elen2 wb_mlen2 Hgv Hwb2 s2 Hwbwf2 Hwbcf2) => Hes2.
  inversion Hsmt. subst. inversion H10. subst.
  { (* True case *)
    inversion H. inversion H0. inversion H5. subst.
    specialize (IH s0 e m elen mlen H6). 
    specialize (IH g2 te2 es2 ubf2 wb_elen2 wb_mlen2 Hwb2 s2 Hwbwf2 Hwbcf2 Hes2).
    case Hpack2: (pack wb_mlen2 wb_elen2 ubf2) => [[pack_s2 pack_e2] pack_m2]. symmetry in Hpack2.
    specialize (IH pack_s2 pack_e2 pack_m2 Hpack2).
    inversion H7. subst.
    specialize (IH s3 e0 m0 elen mlen H9).
    inversion IH. 
    move : H12 => [Helen1 [Hmlen1 [Hs0 [He Hm]]]].
    move : H13 => [Helen2 [Hmlen2 [Hs3 [He0 Hm0]]]].
    
    unfold WBCompare.lt_unpackedbf. 
    inversion Hpack1. inversion Hpack2.
    assert (Hwbelen1 : wb_elen1 > 0). 
    + inversion H11. rewrite -Helen1. auto.
    assert (Hwbmlen1 : wb_mlen1 > 0).
    + inversion H11. rewrite -Hmlen1. auto.
    assert (Hwbelen2 : wb_elen2 > 0). 
    + inversion H4. rewrite -Helen2. auto.
    assert (Hwbmlen2 : wb_mlen2 > 0).
    + inversion H4. rewrite -Hmlen2. auto.
    assert (HwbelenEq : wb_elen1 = wb_elen2).
    + rewrite -Helen1. auto.
    assert (HwbmlenEq : wb_mlen1 = wb_mlen2).
    + rewrite -Hmlen1. auto.
    
    assert (is_ones_zeros_false : forall n, n > 0 -> is_ones (zeros n) = false).
    + destruct n. auto. auto.
    assert (is_zero_ones_false : forall n, n > 0 -> is_zero (ones n) = false). 
    + destruct n. auto. auto.
    
    move : (word_blasting_fp_exp_un_e_range fe1 te s es g Hwf1 Heswf Hescf Hes gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb1 s1 Hwbwf1 Hwbcf1) => He1_range.
    assert (Hnan_flag1 : QFBV.eval_bexp (nan_flag ubf1) s' = QFBV.eval_bexp (nan_flag ubf1) s1). admit.
    assert (Hzero_flag1 : QFBV.eval_bexp (zero_flag ubf1) s' = QFBV.eval_bexp (zero_flag ubf1) s1). admit.
    assert (Hinf_flag1 : QFBV.eval_bexp (inf_flag ubf1) s' = QFBV.eval_bexp (inf_flag ubf1) s1). admit.
    assert (Hun_s1 : QFBV.eval_bexp (un_s ubf1) s' = QFBV.eval_bexp (un_s ubf1) s1). admit.
    assert (Hun_e1 : QFBV.eval_exp (un_e ubf1) s' = QFBV.eval_exp (un_e ubf1) s1). admit.
    assert (Hun_m1 : QFBV.eval_exp (un_m ubf1) s' = QFBV.eval_exp (un_m ubf1) s1). admit.
    assert (Hnan_flag2 : QFBV.eval_bexp (nan_flag ubf2) s' = QFBV.eval_bexp (nan_flag ubf2) s2). admit.
    assert (Hzero_flag2 : QFBV.eval_bexp (zero_flag ubf2) s' = QFBV.eval_bexp (zero_flag ubf2) s2). admit.
    assert (Hinf_flag2 : QFBV.eval_bexp (inf_flag ubf2) s' = QFBV.eval_bexp (inf_flag ubf2) s2). admit.
    assert (Hun_s2 : QFBV.eval_bexp (un_s ubf2) s' = QFBV.eval_bexp (un_s ubf2) s2). admit.
    assert (Hun_e2 : QFBV.eval_exp (un_e ubf2) s' = QFBV.eval_exp (un_e ubf2) s2). admit.
    assert (Hun_m2 : QFBV.eval_exp (un_m ubf2) s' = QFBV.eval_exp (un_m ubf2) s2). admit.
    
    (* both NaN case *)
    simpl.
    case HisNaN1 : (QFBV.eval_bexp (WBClassify.isNaN_unpackedbf wb_mlen1 wb_elen1 ubf1) s'). 
    {
      unfold WBClassify.isNaN_unpackedbf in HisNaN1.
      rewrite H14 in He. rewrite H15 in Hm.
      rewrite He Hm in H8. simpl in H8.
      assert (Hnan_flag' : QFBV.eval_bexp (nan_flag ubf1) s' = QFBV.eval_bexp (nan_flag ubf1) s1). admit.
      rewrite Hnan_flag' in HisNaN1.
      rewrite HisNaN1 in H8. simpl in H8.
      rewrite ones_is_ones in H8.
      rewrite (is_zero_ones_false _ Hwbmlen1) in H8.  discriminate H8.
    }
    case HisNaN2 : (QFBV.eval_bexp (WBClassify.isNaN_unpackedbf wb_mlen2 wb_elen2 ubf2) s'). 
    {
      unfold WBClassify.isNaN_unpackedbf in HisNaN2.
      rewrite H17 in He0. rewrite H18 in Hm0.
      rewrite He0 Hm0 in H3. simpl in H3.
      assert (Hnan_flag' : QFBV.eval_bexp (nan_flag ubf2) s' = QFBV.eval_bexp (nan_flag ubf2) s2). admit.
      rewrite Hnan_flag' in HisNaN2.
      rewrite HisNaN2 in H3. simpl in H3.
      rewrite ones_is_ones in H3.
      rewrite (is_zero_ones_false _ Hwbmlen2) in H3.  discriminate H3.
    }
    
    (* leftZero case *)
    simpl.
    case HisZero1 : (QFBV.eval_bexp (WBClassify.isZero_unpackedbf wb_mlen1 wb_elen1 ubf1) s').
    {
      case HisZero2 : (QFBV.eval_bexp (WBClassify.isZero_unpackedbf wb_mlen2 wb_elen2 ubf2) s').
      {
        rewrite Hnan_flag1 in HisNaN1. rewrite Hzero_flag1 in HisZero1.
        move : (word_blasting_fp_exp_flag_zero_exclusive fe1 te s es g Hwf1 Heswf Hescf Hes gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb1 s1 Hwbwf1 Hwbcf1 HisZero1) => HisInf1.
        apply proj2 in HisInf1.
        rewrite Hnan_flag2 in HisNaN2. rewrite Hzero_flag2 in HisZero2.
        move : (word_blasting_fp_exp_flag_zero_exclusive fe2 te1 s1 es1 g1 Hwf2' Heswf1 Hescf1 Hes1 gen_var g2 te2 es2 ubf2 wb_elen2 wb_mlen2 Hgv Hwb2 s2 Hwbwf2 Hwbcf2 HisZero2) => HisInf2.
        apply proj2 in HisInf2.
        (* 0 < 0, violate H2 *)
        inversion H1. 
        inversion H2.   (* ERlt *)
        {
          rewrite -H21 in H12. rewrite -H22 in H19.
          inversion H12.  (* v_rel *)
          inversion H19.  (* v_rel *)
          { (* both 0 *)
            rewrite -H23 -H28 in H20.
            apply (RIneq.lt_IZR) in H20. discriminate H20.
          }
          { (* fp2 subnormal *)
            injection H29. intros. subst. simpl in H30.
            rewrite HisNaN2 HisZero2 in H30. simpl in H30. 
            rewrite orbT in H30. rewrite zeros_is_zero /= in H30.  
            rewrite Bool.andb_false_r /= in H30. discriminate H30.
          }
          { (* fp2 normal *)
            injection H29. intros. subst. simpl in H30.
            rewrite HisNaN2 HisZero2 in H30. simpl in H30. 
            rewrite HisInf2 in H30. rewrite zeros_is_zero /= in H30.
            rewrite Bool.andb_false_r /= in H30. discriminate H30.
          }
          { (* fp1 subnormal *)
            injection H24. intros. subst. simpl in H25.
            rewrite HisNaN1 HisZero1 in H25. simpl in H25. 
            rewrite HisInf1 in H25.
            rewrite zeros_is_zero /= in H25.
            rewrite zeros_is_zero /= in H25. discriminate H25.
          }
          { (* fp1 normal *)
            injection H24. intros. subst. simpl in H25.
            rewrite HisNaN1 HisZero1 in H25. simpl in H25. 
            rewrite HisInf1 in H25. rewrite zeros_is_zero /= in H25.
            rewrite Bool.andb_false_r /= in H25. discriminate H25.
          }
        }
        { (* RIRN, 0 is not RI *)
          rewrite -H21 in H12. inversion H12.  (* v_rel *)
          {
            (* fp1 inf *)
            injection H25. intros. subst. simpl in H27.
            rewrite HisNaN1 HisZero1 HisInf1 in H27. simpl in H27. 
            rewrite is_ones_zeros_false in H27. discriminate H27. apply Hwbelen2.
          }
          { (* fp1 subnormal *)
            injection H24. intros. subst. simpl in H25.
            rewrite HisNaN1 HisZero1 in H25. simpl in H25. 
            rewrite HisInf1 in H25.
            rewrite zeros_is_zero /= in H25.
            rewrite zeros_is_zero /= in H25. discriminate H25.
          }
          { (* fp1 normal *)
            injection H24. intros. subst. simpl in H25.
            rewrite HisNaN1 HisZero1 in H25. simpl in H25. 
            rewrite HisInf1 in H25. rewrite zeros_is_zero /= in H25.
            rewrite Bool.andb_false_r /= in H25. discriminate H25.
          }
        }
        { (* RNRI, 0 is not RI *)
          rewrite -H22 in H19. inversion H19.  (* v_rel *)
          {
            (* fp2 inf *)
            injection H25. intros. subst. simpl in H27.
            rewrite HisNaN2 HisZero2 HisInf2 in H27. simpl in H27. 
            rewrite is_ones_zeros_false in H27. discriminate H27. apply Hwbelen2.
          }
          { (* fp2 subnormal *)
            injection H24. intros. subst. simpl in H25.
            rewrite HisNaN2 HisZero2 in H25. simpl in H25. 
            rewrite orbT in H25. rewrite zeros_is_zero /= in H25.  
            rewrite Bool.andb_false_r /= in H25. discriminate H25.
          }
          { (* fp2 normal *)
            injection H24. intros. subst. simpl in H25.
            rewrite HisNaN2 HisZero2 in H25. simpl in H25. 
            rewrite HisInf2 in H25. rewrite zeros_is_zero /= in H25.
            rewrite Bool.andb_false_r /= in H25. discriminate H25.
          }
        }
        { (* RIRI, 0 is not RI *)
          rewrite -H21 in H12. inversion H12.  (* v_rel *)
          {
            (* fp1 inf *)
            injection H25. intros. subst. simpl in H27.
            rewrite HisNaN1 HisZero1 HisInf1 in H27. simpl in H27. 
            rewrite is_ones_zeros_false in H27. discriminate H27. apply Hwbelen2.
          }
          { (* fp1 subnormal *)
            injection H24. intros. subst. simpl in H25.
            rewrite HisNaN1 HisZero1 in H25. simpl in H25. 
            rewrite HisInf1 in H25.
            rewrite zeros_is_zero /= in H25.
            rewrite zeros_is_zero /= in H25. discriminate H25.
          }
          { (* fp1 normal *)
            injection H24. intros. subst. simpl in H25.
            rewrite HisNaN1 HisZero1 in H25. simpl in H25. 
            rewrite HisInf1 in H25. rewrite zeros_is_zero /= in H25.
            rewrite Bool.andb_false_r /= in H25. discriminate H25.
          }
        }
      }
      {
        case HisNeg2 : (QFBV.eval_bexp (un_s ubf2) s').
        {
          rewrite Hnan_flag1 in HisNaN1. rewrite Hzero_flag1 in HisZero1.
          move : (word_blasting_fp_exp_flag_zero_exclusive fe1 te s es g Hwf1 Heswf Hescf Hes gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hgv Hwb1 s1 Hwbwf1 Hwbcf1 HisZero1) => HisInf1.
          apply proj2 in HisInf1.
          rewrite Hnan_flag2 in HisNaN2. rewrite Hzero_flag2 in HisZero2.
          rewrite Hun_s2 in HisNeg2.
          (* 0 < -?, violate H2 *)
          inversion H1. 
          inversion H2.   (* ERlt *)
          {
            rewrite -H21 in H12. rewrite -H22 in H19.
            inversion H12.  (* v_rel *)
            inversion H19.  (* v_rel *)
            { (* both 0 *)
              rewrite -H23 -H28 in H20.
              apply (RIneq.lt_IZR) in H20. discriminate H20.
            }
            { (* fp2 subnormal *)
              injection H29. intros. 
              rewrite H16 /= in Hs3. rewrite HisNaN2 HisNeg2 in Hs3.
              rewrite H39 in Hs3. rewrite Hs3 /= in H33.
              
              rewrite -H23 in H20. 
              assert (Hr2 : (r2 < 0)%R). 
              {
                inversion H31. inversion H40. (* exp *)
                rewrite -H44 in H33. inversion H33. (* product1 *)
                 
                inversion H32. (* man *)
                inversion H48. rewrite -H54 in H49. (* denominator *)
                inversion H49.  (* man *)
                inversion H55.  (* inver *)
                + move : (pow_lt 2%R mlen Rlt_0_2) => Hcontra.
                  rewrite -H61 in Hcontra.
                  apply (RIneq.lt_IZR) in Hcontra. discriminate Hcontra.
                + rewrite -H60 in H56. inversion H56.
                  rewrite -H62 -H45 in H34.
                  inversion H34.
                  rewrite Rmult_assoc Ropp_mult_distr_l_reverse.
                  apply Ropp_lt_gt_0_contravar.
                  apply Rmult_gt_0_compat.
                  { apply Rlt_gt. rewrite -INR_IPR. apply pos_INR_nat_of_P. }
                  apply Rmult_gt_0_compat.
                  - apply pow_lt. apply pos_half_prf. 
                  - apply Rmult_gt_0_compat.
                    * rewrite -INR_IZR_INZ.
                      apply Rlt_gt. apply lt_0_INR.
                      apply Nats.ltn_lt. 
                      apply neq_zeros_to_nat_gt0.
                      move : H30 => /andP [He2 Hm2]. 
                      admit. 
                    * apply Rlt_gt. apply Rinv_0_lt_compat.
                       apply pow_lt. apply Rlt_0_2.
              }
              apply Rlt_asym in Hr2. 
              unfold not in Hr2.
              specialize (Hr2 H20). apply (except Hr2).
(*               inversion H31. inversion H40. (* exp *)
              rewrite -H44 in H33. inversion H33. (* product1 *)
              
              rewrite -H37 in H32.
              rewrite Hm0 in H32.
              rewrite -H45 in H34.
              rewrite H18 /= in H32.
              rewrite HisNaN2 HisZero2 in H32.
              
              rewrite -H23 in H20. *)
            }
            { (* fp2 normal *)
              injection H29. intros. 
              rewrite H16 /= in Hs3. rewrite HisNaN2 HisNeg2 in Hs3.
              rewrite H40 in Hs3. rewrite Hs3 /= in H33.
              inversion H31. inversion H41.
              + inversion H45. (* exp *)
                rewrite -H52 in H33. inversion H33. (* product1 *)
                admit.
              + assert (Hinv_er : RN (/ 2) = inv_er).
                {
                  inversion H45. move : Rlt_0_2 => Rlt_0_2.
                  rewrite H52 in Rlt_0_2.
                  apply ROrderedType.ROrder.lt_irrefl in Rlt_0_2.
                  move : Rlt_0_2. apply except. auto.
                }
                rewrite -Hinv_er in H46. inversion H46.
                rewrite -H53 in H33. inversion H33.
                admit.
            }
            { (* fp1 subnormal *)
              injection H24. intros. subst. simpl in H25.
              rewrite HisNaN1 HisZero1 in H25. simpl in H25. 
              rewrite HisInf1 in H25.
              rewrite zeros_is_zero /= in H25.
              rewrite zeros_is_zero /= in H25. discriminate H25.
            }
            { (* fp1 normal *)
              injection H24. intros. subst. simpl in H25.
              rewrite HisNaN1 HisZero1 in H25. simpl in H25. 
              rewrite HisInf1 in H25. rewrite zeros_is_zero /= in H25.
              rewrite Bool.andb_false_r /= in H25. discriminate H25.
            }
          }
          { (* RIRN, 0 is not RI *)
            rewrite -H21 in H12. inversion H12.  (* v_rel *)
            {
              (* fp1 inf *)
              injection H25. intros. subst. simpl in H27.
              rewrite HisNaN1 HisZero1 HisInf1 in H27. simpl in H27. 
              rewrite is_ones_zeros_false in H27. discriminate H27. apply Hwbelen2.
            }
            { (* fp1 subnormal *)
              injection H24. intros. subst. simpl in H25.
              rewrite HisNaN1 HisZero1 in H25. simpl in H25. 
              rewrite HisInf1 in H25.
              rewrite zeros_is_zero /= in H25.
              rewrite zeros_is_zero /= in H25. discriminate H25.
            }
            { (* fp1 normal *)
              injection H24. intros. subst. simpl in H25.
              rewrite HisNaN1 HisZero1 in H25. simpl in H25. 
              rewrite HisInf1 in H25. rewrite zeros_is_zero /= in H25.
              rewrite Bool.andb_false_r /= in H25. discriminate H25.
            }
          }
          { (* RNRI *)
            rewrite -H22 in H19. inversion H19.  (* v_rel *)
            {
              (* fp2 inf , -oo is not +oo *)
              injection H25. intros. 
              rewrite H20 in H23. rewrite -H30 in H23.
              rewrite H16 /= in Hs3. rewrite HisNaN2 HisNeg2 in Hs3.
              rewrite Hs3 /= in H23. discriminate H23. 
            }
            { (* fp2 subnormal, FN < -oo *)
              injection H24. intros. 
              rewrite H16 /= in Hs3. rewrite HisNaN2 HisNeg2 in Hs3.
              rewrite H34 in Hs3. rewrite Hs3 /= in H28.
              inversion H26. inversion H35. (* exp *)
              rewrite -H39 in H28. inversion H28. (* product1 *)
              admit.
            }
            { (* fp2 normal *)
              injection H24. intros. 
              rewrite H16 /= in Hs3. rewrite HisNaN2 HisNeg2 in Hs3.
              rewrite H35 in Hs3. rewrite Hs3 /= in H28.
              inversion H26. inversion H36.
              + inversion H40. (* exp *)
                rewrite -H47 in H28. inversion H28. (* product1 *)
                admit.
              + assert (Hinv_er : RN (/ 2) = inv_er). 
                {
                  inversion H40. move : Rlt_0_2 => Rlt_0_2.
                  rewrite H47 in Rlt_0_2.
                  apply ROrderedType.ROrder.lt_irrefl in Rlt_0_2.
                  move : Rlt_0_2. apply except. auto.
                }
                rewrite -Hinv_er in H41. inversion H41.
                rewrite -H48 in H28. inversion H28.
                admit.
            }
          }
          { (* RIRI, 0 is not RI *)
            rewrite -H21 in H12. inversion H12.  (* v_rel *)
            {
              (* fp1 inf *)
              injection H25. intros. subst. simpl in H27.
              rewrite HisNaN1 HisZero1 HisInf1 in H27. simpl in H27. 
              rewrite is_ones_zeros_false in H27. discriminate H27. apply Hwbelen2.
            }
            { (* fp1 subnormal *)
              injection H24. intros. subst. simpl in H25.
              rewrite HisNaN1 HisZero1 in H25. simpl in H25. 
              rewrite HisInf1 in H25.
              rewrite zeros_is_zero /= in H25.
              rewrite zeros_is_zero /= in H25. discriminate H25.
            }
            { (* fp1 normal *)
              injection H24. intros. subst. simpl in H25.
              rewrite HisNaN1 HisZero1 in H25. simpl in H25. 
              rewrite HisInf1 in H25. rewrite zeros_is_zero /= in H25.
              rewrite Bool.andb_false_r /= in H25. discriminate H25.
            }
          }
        }
        auto.
      }
    }
    
    (* rightZero case *)
    simpl.
    case HisZero2 : (QFBV.eval_bexp (WBClassify.isZero_unpackedbf wb_mlen2 wb_elen2 ubf2) s').
    {
      case HisNeg1 : (QFBV.eval_bexp (un_s ubf1) s').
      auto. 
      {
        (* + ? < 0, violate H2 *)
        rewrite Hnan_flag1 in HisNaN1. rewrite Hzero_flag1 in HisZero1.
        rewrite Hnan_flag2 in HisNaN2. rewrite Hzero_flag2 in HisZero2.
        rewrite Hun_s1 in HisNeg1.
        move : (word_blasting_fp_exp_flag_zero_exclusive fe2 te1 s1 es1 g1 Hwf2' Heswf1 Hescf1 Hes1 gen_var g2 te2 es2 ubf2 wb_elen2 wb_mlen2 Hgv Hwb2 s2 Hwbwf2 Hwbcf2 HisZero2) => HisInf2.
        apply proj2 in HisInf2.
        inversion H1.
        inversion H2.  (* ERlt *)
        { (* RNRN *)
          rewrite -H21 in H12. rewrite -H22 in H19.
          inversion H12.  (* v_rel *)
          inversion H19.  (* v_rel *)
          { (* both 0 *)
            rewrite -H23 -H28 in H20.
            apply (RIneq.lt_IZR) in H20. discriminate H20.
          }
          { (* fp2 subnormal *)
            injection H29. intros. subst. simpl in H30.
            rewrite HisNaN2 HisZero2 in H30. simpl in H30. 
            rewrite orbT in H30. rewrite zeros_is_zero /= in H30.  
            rewrite Bool.andb_false_r /= in H30. discriminate H30.
          }
          { (* fp2 normal *)
            injection H29. intros. subst. simpl in H30.
            rewrite HisNaN2 HisZero2 in H30. simpl in H30. 
            rewrite HisInf2 in H30. rewrite zeros_is_zero /= in H30.
            rewrite Bool.andb_false_r /= in H30. discriminate H30.
          }
          { (* fp1 subnormal *)
              injection H24. intros. 
              rewrite H13 /= in Hs0. rewrite HisNaN1 HisNeg1 in Hs0.
              rewrite H34 in Hs0. rewrite Hs0 /= in H28.
              inversion H26. inversion H35.
              rewrite -H39 in H28. inversion H28. 
              admit.
          }
          { (* fp1 normal *)
            injection H24. intros. 
            rewrite H13 /= in Hs0. rewrite HisNaN1 HisNeg1 in Hs0.
            rewrite H35 in Hs0. rewrite Hs0 /= in H28.
            inversion H26. inversion H36.
            + inversion H40. (* exp *)
              rewrite -H47 in H28. inversion H28. (* product1 *)
              admit.
            + assert (Hinv_er : RN (/ 2) = inv_er).
              {
                inversion H40. move : Rlt_0_2 => Rlt_0_2.
                rewrite H47 in Rlt_0_2.
                apply ROrderedType.ROrder.lt_irrefl in Rlt_0_2.
                move : Rlt_0_2. apply except. auto.
              }
              rewrite -Hinv_er in H41. inversion H41.
              rewrite -H48 in H28. inversion H28. 
              admit.
          }
        }
        { (* RIRN *)
          rewrite -H21 in H12. inversion H12.  (* v_rel *)
          {
            (* fp1 inf , -oo is not +oo *)
            injection H25. intros. 
            rewrite H20 in H23. rewrite -H30 in H23.
            rewrite H13 /= in Hs0. rewrite HisNaN1 HisNeg1 in Hs0.
            rewrite Hs0 /= in H23. discriminate H23. 
          }
          { (* fp1 subnormal, FN < -oo *)
            injection H24. intros. 
            rewrite H13 /= in Hs0. rewrite HisNaN1 HisNeg1 in Hs0.
            rewrite H34 in Hs0. rewrite Hs0 /= in H28.
            inversion H26. inversion H35. (* exp *)
            rewrite -H39 in H28. inversion H28. (* product1 *)
            admit.
          }
          { (* fp1 normal *)
            injection H24. intros. 
            rewrite H13 /= in Hs0. rewrite HisNaN1 HisNeg1 in Hs0.
            rewrite H35 in Hs0. rewrite Hs0 /= in H28.
            inversion H26. inversion H36.
            + inversion H40. (* exp *)
              rewrite -H47 in H28. inversion H28. (* product1 *)
              admit.
            + assert (Hinv_er : RN (/ 2) = inv_er). 
              {
                inversion H40. move : Rlt_0_2 => Rlt_0_2.
                rewrite H47 in Rlt_0_2.
                apply ROrderedType.ROrder.lt_irrefl in Rlt_0_2.
                move : Rlt_0_2. apply except. auto.
              }
              rewrite -Hinv_er in H41. inversion H41.
              rewrite -H48 in H28. inversion H28.
              admit.
          }
        }
        { (* RNRI, 0 is not RI *)
          rewrite -H22 in H19. inversion H19.  (* v_rel *)
          {
            (* fp2 inf *)
            injection H25. intros. subst. simpl in H27.
            rewrite HisNaN2 HisZero2 HisInf2 in H27. simpl in H27. 
            rewrite is_ones_zeros_false in H27. discriminate H27. apply Hwbelen2.
          }
          { (* fp2 subnormal *)
            injection H24. intros. subst. simpl in H25.
            rewrite HisNaN2 HisZero2 in H25. simpl in H25. 
            rewrite HisInf2 in H25.
            rewrite zeros_is_zero /= in H25.
            rewrite zeros_is_zero /= in H25. discriminate H25.
          }
          { (* fp2 normal *)
            injection H24. intros. subst. simpl in H25.
            rewrite HisNaN2 HisZero2 in H25. simpl in H25. 
            rewrite HisInf2 in H25. rewrite zeros_is_zero /= in H25.
            rewrite Bool.andb_false_r /= in H25. discriminate H25.
          }
        }
        { (* RIRI, 0 is not RI *)
          rewrite -H22 in H19. inversion H19.  (* v_rel *)
          {
            (* fp1 inf *)
            injection H25. intros. subst. simpl in H27.
            rewrite HisNaN2 HisZero2 HisInf2 in H27. simpl in H27. 
            rewrite is_ones_zeros_false in H27. discriminate H27. apply Hwbelen2.
          }
          { (* fp1 subnormal *)
            injection H24. intros. subst. simpl in H25.
            rewrite HisNaN2 HisZero2 in H25. simpl in H25. 
            rewrite HisInf2 in H25.
            rewrite zeros_is_zero /= in H25.
            rewrite zeros_is_zero /= in H25. discriminate H25.
          }
          { (* fp1 normal *)
            injection H24. intros. subst. simpl in H25.
            rewrite HisNaN2 HisZero2 in H25. simpl in H25. 
            rewrite HisInf2 in H25. rewrite zeros_is_zero /= in H25.
            rewrite Bool.andb_false_r /= in H25. discriminate H25.
          }
        }
      }
    }
    
    (* leftNegInf case *)
    simpl.
    case HisInf1 : (QFBV.eval_bexp (WBClassify.isInfinite_unpackedbf wb_mlen1 wb_elen1 ubf1) s').
    {
      rewrite Hnan_flag1 in HisNaN1. rewrite Hzero_flag1 in HisZero1.
      rewrite Hinf_flag1 in HisInf1.
      case HisNeg1 : (QFBV.eval_bexp (un_s ubf1) s').
      {
        rewrite Hun_s1 in HisNeg1.
        case HisInf2 : (QFBV.eval_bexp (WBClassify.isInfinite_unpackedbf wb_mlen2 wb_elen2 ubf2) s').
        {
          rewrite Hnan_flag2 in HisNaN2. rewrite Hzero_flag2 in HisZero2.
          rewrite Hinf_flag2 in HisInf2.
          case HisNeg2 : (QFBV.eval_bexp (un_s ubf2) s').
          {
            rewrite Hun_s2 in HisNeg2.
            (* -oo < -oo, violate H2 *)
            inversion H1.
            inversion H2. (* ERlt *)
            { (* RNRN *)
              rewrite -H21 in H12. inversion H12.  (* v_rel *)
              {
                (* fp1 0 *)
                injection H25. intros. subst. simpl in H27.
                rewrite HisNaN1 HisZero1 HisInf1 in H27. simpl in H27. 
                rewrite is_zero_ones_false in H27. discriminate H27. apply Hwbelen2.
              }
              { (* fp1 subnormal *)
                injection H24. intros. subst. simpl in H25.
                rewrite HisNaN1 HisZero1 in H25. simpl in H25. 
                rewrite HisInf1 in H25.
                rewrite zeros_is_zero /= in H25.
                rewrite Bool.andb_false_r /= in H25. discriminate H25.
              }
              { (* fp1 normal *)
                injection H24. intros. subst. simpl in H25.
                rewrite HisNaN1 HisZero1 in H25. simpl in H25. 
                rewrite HisInf1 in H25. rewrite ones_is_ones /= in H25.
                discriminate H25.
              }
            }
            { (* RIRN, RI2 is not RN*)
              rewrite -H22 in H19. inversion H19.  (* v_rel *)
              {
                (* fp2 0 *)
                injection H25. intros. subst. simpl in H27.
                rewrite HisNaN2 HisZero2 HisInf2 in H27. simpl in H27. 
                rewrite is_zero_ones_false in H27. discriminate H27. apply Hwbelen2.
              }
              { (* fp2 subnormal *)
                injection H24. intros. subst. simpl in H25.
                rewrite HisNaN2 HisZero2 HisInf2 in H25. simpl in H25. 
                rewrite is_zero_ones_false in H25. discriminate H25. apply Hwbelen2.
              }
              { (* fp2 normal *)
                injection H24. intros. subst. simpl in H25.
                rewrite HisNaN2 HisZero2 HisInf2 in H25. simpl in H25. 
                rewrite ones_is_ones in H25. discriminate H25. 
              }
            }
            { (* RNRI, RI1 is not RN *)
              rewrite -H21 in H12. inversion H12.  (* v_rel *)
              {
                (* fp1 0 *)
                injection H25. intros. subst. simpl in H27.
                rewrite HisNaN1 HisZero1 HisInf1 in H27. simpl in H27. 
                rewrite is_zero_ones_false in H27. discriminate H27. apply Hwbelen2.
              }
              { (* fp1 subnormal *)
                injection H24. intros. subst. simpl in H25.
                rewrite HisNaN1 HisZero1 HisInf1 in H25. simpl in H25. 
                rewrite is_zero_ones_false in H25. discriminate H25. apply Hwbelen2.
              }
              { (* fp1 normal *)
                injection H24. intros. subst. simpl in H25.
                rewrite HisNaN1 HisZero1 HisInf1 in H25. simpl in H25. 
                rewrite ones_is_ones in H25. discriminate H25. 
              }
            }
            { (* RIRI *)
              rewrite -H22 in H19. inversion H19.
              { (* fp2 -oo *)
                injection H25. intros.
                rewrite H16 /= in Hs3. rewrite HisNaN2 HisNeg2 in Hs3.
                rewrite H30 in Hs3. rewrite Hs3 /= in H23. 
                rewrite -H23 /= in H20. replace (msb [::true]) with true in H20 by auto.
                inversion H20. discriminate H32.
              }
              { (* fp2 subnormal *)
                injection H24. intros. subst. simpl in H25.
                rewrite HisNaN2 HisZero2 HisInf2 in H25. simpl in H25. 
                rewrite is_zero_ones_false in H25. discriminate H25. apply Hwbelen2.
              }
              { (* fp2 normal *)
                injection H24. intros. subst. simpl in H25.
                rewrite HisNaN2 HisZero2 HisInf2 in H25. simpl in H25. 
                rewrite ones_is_ones in H25. discriminate H25. 
              }
            }
          }
          auto.
        }
        auto.
      }
      {
        rewrite Hun_s1 in HisNeg1.
        (* +oo < ?, violate H2 *)
        inversion H1. inversion H2.
        { (* RNRN *)
          rewrite -H21 in H12. inversion H12. 
          {
            (* fp1 0 *)
            injection H25. intros. subst. simpl in H27.
            rewrite HisNaN1 HisZero1 HisInf1 in H27. simpl in H27. 
            rewrite is_zero_ones_false in H27. discriminate H27. apply Hwbelen2.
          }
          { (* fp1 subnormal *)
            injection H24. intros. subst. simpl in H25.
            rewrite HisNaN1 HisZero1 in H25. simpl in H25. 
            rewrite HisInf1 in H25.
            rewrite zeros_is_zero /= in H25.
            rewrite Bool.andb_false_r /= in H25. discriminate H25.
          }
          { (* fp1 normal *)
            injection H24. intros. subst. simpl in H25.
            rewrite HisNaN1 HisZero1 in H25. simpl in H25. 
            rewrite HisInf1 in H25. rewrite ones_is_ones /= in H25.
            discriminate H25.
          }
        }
        { (* RIRN *)
          rewrite -H21 in H12. 
          inversion H12. 
          { (* fp1 -oo,*)
            injection H25. intros.
            rewrite H13 /= in Hs0. rewrite HisNaN1 HisNeg1 in Hs0.
            rewrite H30 in Hs0. rewrite Hs0 /= in H23. 
            rewrite -H23 /= in H20. replace (msb [::false]) with false in H20 by auto.
            discriminate H20.
          }
          { (* fp1 subnormal *)
            injection H24. intros. subst. simpl in H25.
            rewrite HisNaN1 HisZero1 in H25. simpl in H25. 
            rewrite HisInf1 in H25.
            rewrite zeros_is_zero /= in H25.
            rewrite Bool.andb_false_r /= in H25. discriminate H25.
          }
          { (* fp1 normal *)
            injection H24. intros. subst. simpl in H25.
            rewrite HisNaN1 HisZero1 in H25. simpl in H25. 
            rewrite HisInf1 in H25. rewrite ones_is_ones /= in H25.
            discriminate H25.
          }
        }
        { (* RNRI *)
          rewrite -H21 in H12. inversion H12.  (* v_rel *)
          {
            (* fp1 0 *)
            injection H25. intros. subst. simpl in H27.
            rewrite HisNaN1 HisZero1 HisInf1 in H27. simpl in H27. 
            rewrite is_zero_ones_false in H27. discriminate H27. apply Hwbelen2.
          }
          { (* fp1 subnormal *)
            injection H24. intros. subst. simpl in H25.
            rewrite HisNaN1 HisZero1 HisInf1 in H25. simpl in H25. 
            rewrite is_zero_ones_false in H25. discriminate H25. apply Hwbelen2.
          }
          { (* fp1 normal *)
            injection H24. intros. subst. simpl in H25.
            rewrite HisNaN1 HisZero1 HisInf1 in H25. simpl in H25. 
            rewrite ones_is_ones in H25. discriminate H25. 
          }
        }
        { (* RIRI *)
          rewrite -H21 in H12. inversion H12.
          { (* +oo < _, *)
            injection H25. intros.
            rewrite H13 /= in Hs0. rewrite HisNaN1 HisNeg1 in Hs0.
            rewrite H30 in Hs0. rewrite Hs0 /= in H23. 
            rewrite -H23 /= in H20. replace (msb [::true]) with true in H20 by auto.
            inversion H20. discriminate H31.
          }
          { (* fp1 subnormal *)
            injection H24. intros. subst. simpl in H25.
            rewrite HisNaN1 HisZero1 HisInf1 in H25. simpl in H25. 
            rewrite is_zero_ones_false in H25. discriminate H25. apply Hwbelen2.
          }
          { (* fp1 normal *)
            injection H24. intros. subst. simpl in H25.
            rewrite HisNaN1 HisZero1 HisInf1 in H25. simpl in H25. 
            rewrite ones_is_ones in H25. discriminate H25. 
          }
        }
      }
    }
    
    (* rightPosInf case *)
    simpl.
    case HisInf2 : (QFBV.eval_bexp (WBClassify.isInfinite_unpackedbf wb_mlen2 wb_elen2 ubf2) s').
    {
      rewrite Hnan_flag2 in HisNaN2. rewrite Hzero_flag2 in HisZero2.
      rewrite Hinf_flag2 in HisInf2.
      case HisNeg2 : (QFBV.eval_bexp (un_s ubf2) s').
      {
        rewrite Hun_s2 in HisNeg2.
        (* ? < -oo, violate H2 *)
        inversion H1.
        inversion H2.
        { (* RNRN *)
          rewrite -H22 in H19. inversion H19.  (* v_rel *)
          {
            (* fp2 inf *)
            injection H25. intros. subst. simpl in H27.
            rewrite HisNaN2 HisZero2 HisInf2 in H27. simpl in H27. 
            rewrite is_zero_ones_false in H27. discriminate H27. apply Hwbelen2.
          }
          { (* fp2 subnormal *)
            injection H24. intros. subst. simpl in H25.
            rewrite HisNaN2 HisZero2 in H25. simpl in H25. 
            rewrite HisInf2 in H25.
            rewrite zeros_is_zero /= in H25.
            rewrite Bool.andb_false_r /= in H25. discriminate H25.
          }
          { (* fp2 normal *)
            injection H24. intros. subst. simpl in H25.
            rewrite HisNaN2 HisZero2 in H25. simpl in H25. 
            rewrite HisInf2 in H25. rewrite ones_is_ones /= in H25.
            discriminate H25.
          }
        }
        { (* RIRN *)
          rewrite -H22 in H19. inversion H19.  (* v_rel *)
          {
            (* fp2 0 *)
            injection H25. intros. subst. simpl in H27.
            rewrite HisNaN2 HisZero2 HisInf2 in H27. simpl in H27. 
            rewrite is_zero_ones_false in H27. discriminate H27. apply Hwbelen2.
          }
          { (* fp2 subnormal *)
            injection H24. intros. subst. simpl in H25.
            rewrite HisNaN2 HisZero2 HisInf2 in H25. simpl in H25. 
            rewrite is_zero_ones_false in H25. discriminate H25. apply Hwbelen2.
          }
          { (* fp2 normal *)
            injection H24. intros. subst. simpl in H25.
            rewrite HisNaN2 HisZero2 HisInf2 in H25. simpl in H25. 
            rewrite ones_is_ones in H25. discriminate H25. 
          }
        }
        { (* RNRI *)
          rewrite -H22 in H19. inversion H19.
          { (* fp2 +oo *)
            injection H25. intros.
            rewrite H16 /= in Hs3. rewrite HisNaN2 HisNeg2 in Hs3.
            rewrite H30 in Hs3. rewrite Hs3 /= in H23.
            rewrite -H23 in H20. replace (msb [::true]) with true in H20 by auto.
            discriminate H20.
          }
          { (* fp2 subnormal *)
            injection H24. intros. subst. simpl in H25.
            rewrite HisNaN2 HisZero2 HisInf2 in H25. simpl in H25. 
            rewrite is_zero_ones_false in H25. discriminate H25. apply Hwbelen2.
          }
          { (* fp1 normal *)
            injection H24. intros. subst. simpl in H25.
            rewrite HisNaN2 HisZero2 HisInf2 in H25. simpl in H25. 
            rewrite ones_is_ones in H25. discriminate H25. 
          }
        }
        { (* RIRI *)
          rewrite -H22 in H19. inversion H19.
          { (* fp2 +oo *)
            injection H25. intros.
            rewrite H16 /= in Hs3. rewrite HisNaN2 HisNeg2 in Hs3.
            rewrite H30 in Hs3. rewrite Hs3 /= in H23.
            rewrite -H23 in H20. replace (msb [::true]) with true in H20 by auto.
            inversion H20. discriminate H32.
          }
          { (* fp2 subnormal *)
            injection H24. intros. subst. simpl in H25.
            rewrite HisNaN2 HisZero2 HisInf2 in H25. simpl in H25. 
            rewrite is_zero_ones_false in H25. discriminate H25. apply Hwbelen2.
          }
          { (* fp1 normal *)
            injection H24. intros. subst. simpl in H25.
            rewrite HisNaN2 HisZero2 HisInf2 in H25. simpl in H25. 
            rewrite ones_is_ones in H25. discriminate H25. 
          }
        }
      }
      auto.
    }
    
    (* normal case *)
    rewrite Hnan_flag1 in HisNaN1. rewrite Hinf_flag1 in HisInf1. rewrite Hzero_flag1 in HisZero1.
    rewrite Hnan_flag2 in HisNaN2. rewrite Hinf_flag2 in HisInf2. rewrite Hzero_flag2 in HisZero2.
    simpl.
    rewrite subnn. rewrite sext0 sext0 sext0 sext0. 
    case HisNormal : 
     ((sleB (unpack_elen wb_mlen1 wb_elen1) -bits of Z (min_normal_e wb_elen1)%bits
     (QFBV.eval_exp (un_e ubf1) s') &&
   sleB (QFBV.eval_exp (un_e ubf1) s')
     (unpack_elen wb_mlen1 wb_elen1) -bits of Z (max_normal_e wb_elen1)%bits
   || sleB
        (unpack_elen wb_mlen1 wb_elen1) -bits of Z (min_subnormal_e wb_mlen1 wb_elen1)%bits
        (QFBV.eval_exp (un_e ubf1) s') &&
      sleB (QFBV.eval_exp (un_e ubf1) s')
        (unpack_elen wb_mlen1 wb_elen1) -bits of Z (max_subnormal_e wb_elen1)%bits) &&
  (sleB (unpack_elen wb_mlen1 wb_elen1) -bits of Z (min_normal_e wb_elen1)%bits
     (QFBV.eval_exp (un_e ubf2) s') &&
   sleB (QFBV.eval_exp (un_e ubf2) s')
     (unpack_elen wb_mlen1 wb_elen1) -bits of Z (max_normal_e wb_elen1)%bits
   || sleB
        (unpack_elen wb_mlen1 wb_elen1) -bits of Z (min_subnormal_e wb_mlen1 wb_elen1)%bits
        (QFBV.eval_exp (un_e ubf2) s') &&
      sleB (QFBV.eval_exp (un_e ubf2) s')
        (unpack_elen wb_mlen1 wb_elen1) -bits of Z (max_subnormal_e wb_elen1)%bits)).
    {
      rewrite Hun_e1 Hun_e2 in HisNormal.
      move : HisNormal => /andP [HisNormal1 HisNormal2].
      case HisNeg1 : (QFBV.eval_bexp (un_s ubf1) s').
      {
        rewrite Hun_s1 in HisNeg1.
        case HisNeg2 : (QFBV.eval_bexp (un_s ubf2) s').
        {
          rewrite Hun_s2 in HisNeg2.
          case He1Gte2 : (sgtB (QFBV.eval_exp (un_e ubf1) s') (QFBV.eval_exp (un_e ubf2) s')).
          auto.
          {
            rewrite Hun_e1 Hun_e2 in He1Gte2.
            simpl.
            case He1Eqe2 : ((QFBV.eval_exp (un_e ubf1) s' == QFBV.eval_exp (un_e ubf2) s')).
            {
              rewrite Hun_e1 Hun_e2 in He1Eqe2.
              case Hm1Gtm2 : (sgtB (QFBV.eval_exp (un_m ubf1) s') (QFBV.eval_exp (un_m ubf2) s')).
              auto.
              {
                rewrite Hun_m1 Hun_m2 in Hm1Gtm2.
                (* s1 = neg, s2 = neg, e1 = e2, m1 <= m2, violate H2 *)
                inversion H1.
                inversion H2.
                { (* RNRN *)
                  rewrite -H21 in H12. rewrite -H22 in H19.
                  inversion H12. inversion H19.
                  { (* both 0 *)
                    rewrite -H23 -H28 in H20.
                    apply (RIneq.lt_IZR) in H20. discriminate H20.
                  }
                  { (* fp1 0, fp2 subnormal *)
                    admit.
                  }
                  { (* fp1 0, fp2 normal *)
                    admit.
                  }
                  { (* fp1 subnormal *)
                    inversion H19. 
                    { (* fp2 0 *)
                      admit.
                    }
                    { (* fp2 subnormal *)
                      injection H24. intros.
                      injection H33. intros.
                      assert (Hmsize : size m1 = size m2). 
                      {
                        inversion H23. inversion H32.
                        rewrite H41 in H57. rewrite H44 in H68.
                        rewrite H57 H68 //=.
                      }
                      rewrite He in H42. rewrite H14 /= in H42.
                      rewrite HisNaN1 HisZero1 HisInf1 in H42.
                      rewrite subnn in H42. rewrite sext0 sext0 in H42.
                      case HisNormal1' : (sleB (unpack_elen wb_mlen1 wb_elen1) -bits of Z (min_normal_e wb_elen1)%bits
           (QFBV.eval_exp (un_e ubf1) s1) &&
         sleB (QFBV.eval_exp (un_e ubf1) s1)
           (unpack_elen wb_mlen1 wb_elen1) -bits of Z (max_normal_e wb_elen1)%bits).
                      { (* violate H25, e1 is not zero. the similar proof is in fp.is* *)
                        rewrite HisNormal1' /= in H42.
                        admit. 
                      }
                      rewrite HisNormal1' /= in H42.
                      rewrite Hm in H41. rewrite H15 /= in H41.
                      rewrite HisNaN1 HisZero1 HisInf1 in H41.
                      rewrite subnn in H41. rewrite sext0 sext0 in H41.
                      rewrite HisNormal1' /= in H41.
                      
                      rewrite He0 in H45. rewrite H17 /= in H45.
                      rewrite HisNaN2 HisZero2 HisInf2 in H45.
                      rewrite subnn in H45. rewrite sext0 sext0 in H45.
                      case HisNormal2' : (sleB
                                           (unpack_elen wb_mlen2 wb_elen2) -bits
                                           of Z (min_normal_e wb_elen2)%bits
                                           (QFBV.eval_exp (un_e ubf2) s2) &&
                                         sleB (QFBV.eval_exp (un_e ubf2) s2)
                                           (unpack_elen wb_mlen2 wb_elen2) -bits
                                           of Z (max_normal_e wb_elen2)%bits).
                      { (* violate H34, e2 is not zero. the similar proof is in fp.is* *)
                        rewrite HisNormal2' /= in H45.
                        admit. 
                      }
                      rewrite HisNormal2' /= in H45.
                      rewrite Hm0 in H44. rewrite H18 /= in H44.
                      rewrite HisNaN2 HisZero2 HisInf2 in H44.
                      rewrite subnn in H44. rewrite sext0 sext0 in H44.
                      rewrite HisNormal2' /= in H44.
                      
                      assert (leB m1 m2). 
                      {
                        admit.
                      }
                      rewrite -HwbelenEq H42 in H45. 
                      
                      rewrite H13 /= in Hs0. rewrite HisNaN1 HisNeg1 in Hs0.
                      rewrite H16 /= in Hs3. rewrite HisNaN2 HisNeg2 in Hs3.
                      rewrite H43 in Hs0. rewrite Hs0 /= in H28.
                      rewrite H46 in Hs3. rewrite Hs3 /= in H37.
                      
                      inversion H26. inversion H48. rewrite -H52 in H28. (* exp *)
                      inversion H35. inversion H53. rewrite -H57 in H37. (* exp0 *)
                      
                      inversion H28. rewrite -H58 in H29. (* product1 *)
                      inversion H37. rewrite -H61 in H38. (* product0 *)
                      
                      inversion H27. inversion H64. rewrite -H70 in H65.
                      inversion H65. inversion H71.
                      + move : (pow_lt 2%R mlen Rlt_0_2) => Hcontra.
                        apply Rlt_not_eq in Hcontra.
                        rewrite H77 in Hcontra.
                        admit.
                      rewrite -H76 in H72. inversion H72. (* man *)
                      rewrite -H78 in H29. inversion H29. (* H84 r1 *)
                      
                      inversion H36. inversion H81. rewrite -H90 in H85.
                      inversion H85. inversion H91.
                      + move : (pow_lt 2%R mlen Rlt_0_2) => Hcontra.
                        apply Rlt_not_eq in Hcontra.
                        rewrite H97 in Hcontra.
                        admit.
                      rewrite -H96 in H92. inversion H92. (* man *)
                      rewrite -H98 in H38. inversion H38. (* H104 r1 *)
                      
                      rewrite -H84 -H104 in H20.
                      rewrite Rmult_assoc Ropp_mult_distr_l_reverse in H20.
                      rewrite Rmult_assoc Ropp_mult_distr_l_reverse in H20.
                      apply Ropp_gt_lt_contravar in H20.
                      rewrite Ropp_involutive Ropp_involutive in H20.
                      replace (IPR 1) with 1%R in H20 by auto.
                      rewrite Rmult_1_l Rmult_1_l in H20.
                      apply (Rmult_lt_reg_l ((/ 2) ^ (SMTLIBfp.bias elen - 1))) in H20.
                      apply (Rmult_lt_reg_r (/ 2 ^ mlen)) in H20.
                      {
                        apply lt_IZR in H20. rewrite -to_Zpos_nat -to_Zpos_nat in H20.
                        apply to_Zpos_ltB in H20. 
                        move : leBNlt => Hcontra.
                        specialize (Hcontra m1 m2 Hmsize).
                        rewrite Hcontra in H47.
                        assert (Hcontra' : ~~ (m2 <# m1)%bits && (m2 <# m1)%bits). 
                        + apply /andP. split. auto. auto.
                        rewrite Bool.andb_negb_l in Hcontra'. discriminate Hcontra'.
                      }
                      + apply Rinv_0_lt_compat. apply pow_lt. apply Rlt_0_2.
                      + apply pow_lt. apply Rinv_0_lt_compat. apply Rlt_0_2.
                    } 
                    { (* fp2 normal *)
                      injection H24. intros.
                      injection H33. intros.
                      rewrite He in H43. rewrite H14 /= in H43.
                      rewrite HisNaN1 HisZero1 HisInf1 in H43.
                      rewrite subnn in H43. rewrite sext0 sext0 in H43.
                      case HisNormal1' : (sleB (unpack_elen wb_mlen1 wb_elen1) -bits of Z (min_normal_e wb_elen1)%bits
           (QFBV.eval_exp (un_e ubf1) s1) &&
         sleB (QFBV.eval_exp (un_e ubf1) s1)
           (unpack_elen wb_mlen1 wb_elen1) -bits of Z (max_normal_e wb_elen1)%bits).
                      { (* violate H25, e1 is not zero. the similar proof is in fp.is* *)
                        rewrite HisNormal1' /= in H43.
                        admit. 
                      }
                      rewrite HisNormal1' /= in H43.
                      
                      case HisNormal2' : (sleB
                         (unpack_elen wb_mlen1 wb_elen1) -bits
                         of Z (min_normal_e wb_elen1)%bits
                         (QFBV.eval_exp (un_e ubf2) s2) &&
                       sleB (QFBV.eval_exp (un_e ubf2) s2)
                         (unpack_elen wb_mlen1 wb_elen1) -bits
                         of Z (max_normal_e wb_elen1)%bits).
                      {
                        assert (He1Eqe2' : (QFBV.eval_exp (un_e ubf1) s1) = (QFBV.eval_exp (un_e ubf2) s2)).
                        {
                          admit.
                        }
                        rewrite -He1Eqe2' in HisNormal2'. rewrite HisNormal1' in HisNormal2'.
                        discriminate HisNormal2'.
                      }
                      {
                        (* violate H34, e2 is zero. *)
                        rewrite He0 in H46. rewrite H17 /= in H46.
                        rewrite HisNaN2 HisZero2 HisInf2 in H46.
                        rewrite subnn in H46. rewrite sext0 sext0 in H46.
                        rewrite HwbelenEq HwbmlenEq in HisNormal2'. rewrite HisNormal2' /= in H46.
                        rewrite -H46 in H34. rewrite zeros_is_zero /= in H34.
                        rewrite Bool.andb_false_r in H34. discriminate H34.
                      }
                    }
                  }
                  { (* fp1 normal *)
                    inversion H19.
                    { (* fp2 0 *)
                      admit.
                    } 
                    { (* fp2 subnormal *)
                      admit.
                    }
                    { (* fp2 normal *)
                      injection H24. intros.
                      injection H34. intros.
                      rewrite He in H44. rewrite H14 /= in H44.
                      rewrite HisNaN1 HisZero1 HisInf1 in H44.
                      rewrite subnn in H44. rewrite sext0 sext0 in H44.
                      case HisNormal1' : (sleB (unpack_elen wb_mlen1 wb_elen1) -bits of Z (min_normal_e wb_elen1)%bits
           (QFBV.eval_exp (un_e ubf1) s1) &&
         sleB (QFBV.eval_exp (un_e ubf1) s1)
           (unpack_elen wb_mlen1 wb_elen1) -bits of Z (max_normal_e wb_elen1)%bits).
                      rewrite HisNormal1' /= in H44.
                      rewrite Hm in H43. rewrite H15 /= in H43.
                      rewrite HisNaN1 HisZero1 HisInf1 in H43.
                      rewrite subnn in H43. rewrite sext0 sext0 in H43.
                      rewrite HisNormal1' /= in H43.
                      
                      rewrite He0 in H47. rewrite H17 /= in H47.
                      rewrite HisNaN2 HisZero2 HisInf2 in H47.
                      rewrite subnn in H47. rewrite sext0 sext0 in H47.
                      case HisNormal2' : (sleB
                                           (unpack_elen wb_mlen2 wb_elen2) -bits
                                           of Z (min_normal_e wb_elen2)%bits
                                           (QFBV.eval_exp (un_e ubf2) s2) &&
                                         sleB (QFBV.eval_exp (un_e ubf2) s2)
                                           (unpack_elen wb_mlen2 wb_elen2) -bits
                                           of Z (max_normal_e wb_elen2)%bits).
                      rewrite HisNormal2' /= in H47.
                      rewrite Hm0 in H46. rewrite H18 /= in H46.
                      rewrite HisNaN2 HisZero2 HisInf2 in H46.
                      rewrite subnn in H46. rewrite sext0 sext0 in H46.
                      rewrite HisNormal2' /= in H46.
                      assert (leB m1 m2). 
                      {
                        rewrite -H43 -H46. admit.
                      }
                      
                      rewrite H13 /= in Hs0. rewrite HisNaN1 HisNeg1 in Hs0.
                      rewrite H16 /= in Hs3. rewrite HisNaN2 HisNeg2 in Hs3.
                      rewrite H45 in Hs0. rewrite Hs0 /= in H28.
                      rewrite H48 in Hs3. rewrite Hs3 /= in H38.
                      
                      inversion H26. rewrite -H44 in H50. inversion H50. inversion H54. rewrite -H61 in H28. (* exp *)
                      {
                        inversion H36. rewrite -H47 in H62. inversion H62. inversion H66. rewrite -H73 in H38. (* exp0 *)
                        {
                          inversion H27. inversion H74. rewrite -H80 in H75. rewrite -H43 in H75. inversion H75.  
                          inversion H81.
                          + move : (pow_lt 2%R mlen Rlt_0_2) => Hcontra.
                            apply Rlt_not_eq in Hcontra.
                            rewrite H87 in Hcontra. admit.
                          rewrite -H86 in H82. inversion H82. (* H88 man *)
                          inversion H28. rewrite -H91 in H29. (* product1 *)
                          rewrite -H88 in H29. inversion H29. (* H94 product2 *)
                          rewrite -H94 in H30. inversion H30. (* H100 r1 *)
                          
                          inversion H37. inversion H97. rewrite -H106 in H101. inversion H101.
                          inversion H107.
                          + move : (pow_lt 2%R mlen Rlt_0_2) => Hcontra.
                            apply Rlt_not_eq in Hcontra.
                            rewrite H113 in Hcontra. admit.
                          rewrite -H112 in H108. inversion H108. (* H114 man0 *)
                          inversion H38. rewrite -H117 in H39. (* product1 *)
                          rewrite -H114 in H39. inversion H39. (* H120 product3 *)
                          rewrite -H120 in H40. inversion H40. (* H126 r2 *)
                          rewrite -H100 -H126 -H46 in H20.
                       	  admit.   
                        }
                        {
                          (* H53 and H65 conflict *)
                          admit.
                        }
                      }
                      {
                        rewrite -H47 in H36. inversion H36. inversion H60. 
                        {
                          (* H53 and H63 conflict *)
                          admit.
                        }
                        {
                          admit.
                        }
                      }
                      admit. admit.
                    }
                  }
                }
                admit. admit. admit.
              }
            }
            {
              (* s1 = neg, s2 = neg, e1 < e2, violate H2 *)
              admit.
            }
          }
        }
        auto.
      }
      {
        case HisNeg2 : (QFBV.eval_bexp (un_s ubf2) s').
        {
          (* + _ < - _, violate H2 *)
          admit.
        }
        {
          simpl.
          case He1Lte2 : (sltB (QFBV.eval_exp (un_e ubf1) s') (QFBV.eval_exp (un_e ubf2) s')).
          auto.
          {
            case He1Eqe2 : (QFBV.eval_exp (un_e ubf1) s' == QFBV.eval_exp (un_e ubf2) s').
            {
              case Hm1Ltm2 : (sltB (QFBV.eval_exp (un_m ubf1) s') (QFBV.eval_exp (un_m ubf2) s')).
              auto.
              {
                (* s1 = Pos, s2 = Pos, e1 = e2, m1 >= m2, violate H2 *)
                admit.
              }
            }
            {
              (* s1 = pos, s2 = pos, e1 > e2, violate H2 *)
              admit.
            }
          }
        }
      }
    }
    
    (* other false case *)
    simpl.
(*     rewrite Hnan_flag1 in HisNaN1. rewrite Hzero_flag1 in HisZero1.
    rewrite Hinf_flag1 in HisInf1. *)
    specialize (He1_range HisNaN1 HisZero1 HisInf1).
    simpl in He1_range.  rewrite HisNaN1 HisZero1 HisInf1 in He1_range. 
    simpl in He1_range. 
    rewrite subnn in He1_range. rewrite sext0 sext0 sext0 sext0 in He1_range.
    rewrite Hun_e1 in HisNormal. rewrite He1_range in HisNormal. 
    
    move : (word_blasting_fp_exp_un_e_range fe2 te1 s1 es1 g1 Hwf2' Heswf1 Hescf1 Hes1 gen_var g2 te2 es2 ubf2 wb_elen2 wb_mlen2 Hgv Hwb2 s2 Hwbwf2 Hwbcf2) => He2_range.
(*     rewrite Hnan_flag2 in HisNaN2. rewrite Hzero_flag2 in HisZero2.
    rewrite Hinf_flag2 in HisInf2. *)
    specialize (He2_range HisNaN2 HisZero2 HisInf2).
    simpl in He2_range.  rewrite HisNaN2 HisZero2 HisInf2 in He2_range. 
    simpl in He2_range. 
    rewrite subnn in He2_range. rewrite sext0 sext0 sext0 sext0 in He2_range.
    rewrite Hun_e2 in HisNormal. rewrite HwbelenEq HwbmlenEq in HisNormal.
    rewrite He2_range in HisNormal. 
    discriminate HisNormal.
  }
  { (* False case *)
    unfold fbbinop_denote_smtlib in H.
    unfold not in H.
    admit.
  }
Admitted.

Lemma word_blasting_fp_bexp_semantics_equivalence_gt :
  forall fe1 fe2: Fq2bvq.fp_exp,
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_exp fe1 te0 ->
      Fq2bvq.well_formed_fp_exp fe2 te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1,
            valid_gen_var gen_var ->
              (te1, g1, es1, ubf1, wb_elen1, wb_mlen1) = word_blast_exp gen_var g0 es0 te0 fe1 ->
                forall s1 : SSAStore.t,
                  well_formed_bexps es1 te1 && Fq2bvq.well_formed_unpackedbf ubf1 te1 ->
                  conformed_bexps es1 s1 te1 && Fq2bvq.conform_unpackedbf ubf1 s1 te1 ->
                  eval_bexps es1 s1 ->
                    forall pack_s1 pack_e1 pack_m1, 
                      (pack_s1, pack_e1, pack_m1) = pack wb_mlen1 wb_elen1 ubf1 ->
                        forall smt_s1 smt_e1 smt_m1 elen1 mlen1,
                          eval_fp_exp fe1 s0 (SMTLIBfp.ieee754_fp smt_s1 smt_e1 smt_m1) elen1 mlen1 ->
          forall g2 te2 es2 ubf2 wb_elen2 wb_mlen2,
              (te2, g2, es2, ubf2, wb_elen2, wb_mlen2) = word_blast_exp gen_var g1 es1 te1 fe2 ->
                forall s2 : SSAStore.t,
                  well_formed_bexps es2 te2 && Fq2bvq.well_formed_unpackedbf ubf2 te2 ->
                  conformed_bexps es2 s2 te2 && Fq2bvq.conform_unpackedbf ubf2 s2 te2 ->
                  eval_bexps es2 s2 ->
                    forall pack_s2 pack_e2 pack_m2, 
                      (pack_s2, pack_e2, pack_m2) = pack wb_mlen2 wb_elen2 ubf2 ->
                        forall smt_s2 smt_e2 smt_m2 elen2 mlen2,
                          eval_fp_exp fe2 s0 (SMTLIBfp.ieee754_fp smt_s2 smt_e2 smt_m2) elen2 mlen2 ->
                            (elen1 = wb_elen1 /\
                            mlen1 = wb_mlen1 /\
                            smt_s1 = (QFBV.eval_exp pack_s1 s1) /\ 
                            smt_e1 = (QFBV.eval_exp pack_e1 s1) /\ 
                            smt_m1 = (QFBV.eval_exp pack_m1 s1)) /\ 
                            (elen2 = wb_elen2 /\
                            mlen2 = wb_mlen2 /\
                            smt_s2 = (QFBV.eval_exp pack_s2 s2) /\ 
                            smt_e2 = (QFBV.eval_exp pack_e2 s2) /\ 
                            smt_m2 = (QFBV.eval_exp pack_m2 s2))) -> 
    forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
      Fq2bvq.well_formed_fp_bexp (Fq2bvq.FBbinop Fq2bvq.FBgt fe1 fe2) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' b,
              valid_gen_var gen_var ->
                (te', g', es', b) = word_blast_bexp gen_var g es te (Fq2bvq.FBbinop Fq2bvq.FBgt fe1 fe2) ->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && QFBV.well_formed_bexp b te' ->
                    conformed_bexps es' s' te' && conform_bexp b s' te' ->
                    eval_bexps es' s' ->
                      forall smt_b, eval_fp_bexp (Fq2bvq.FBbinop Fq2bvq.FBeq fe1 fe2) s smt_b ->
                        smt_b = QFBV.eval_bexp b s'.
Proof.
Admitted.

Lemma word_blasting_fp_bexp_semantics_equivalence_leq :
  forall fe1 fe2: Fq2bvq.fp_exp,
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_exp fe1 te0 ->
      Fq2bvq.well_formed_fp_exp fe2 te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1,
            valid_gen_var gen_var ->
              (te1, g1, es1, ubf1, wb_elen1, wb_mlen1) = word_blast_exp gen_var g0 es0 te0 fe1 ->
                forall s1 : SSAStore.t,
                  well_formed_bexps es1 te1 && Fq2bvq.well_formed_unpackedbf ubf1 te1 ->
                  conformed_bexps es1 s1 te1 && Fq2bvq.conform_unpackedbf ubf1 s1 te1 ->
                  eval_bexps es1 s1 ->
                    forall pack_s1 pack_e1 pack_m1, 
                      (pack_s1, pack_e1, pack_m1) = pack wb_mlen1 wb_elen1 ubf1 ->
                        forall smt_s1 smt_e1 smt_m1 elen1 mlen1,
                          eval_fp_exp fe1 s0 (SMTLIBfp.ieee754_fp smt_s1 smt_e1 smt_m1) elen1 mlen1 ->
          forall g2 te2 es2 ubf2 wb_elen2 wb_mlen2,
              (te2, g2, es2, ubf2, wb_elen2, wb_mlen2) = word_blast_exp gen_var g1 es1 te1 fe2 ->
                forall s2 : SSAStore.t,
                  well_formed_bexps es2 te2 && Fq2bvq.well_formed_unpackedbf ubf2 te2 ->
                  conformed_bexps es2 s2 te2 && Fq2bvq.conform_unpackedbf ubf2 s2 te2 ->
                  eval_bexps es2 s2 ->
                    forall pack_s2 pack_e2 pack_m2, 
                      (pack_s2, pack_e2, pack_m2) = pack wb_mlen2 wb_elen2 ubf2 ->
                        forall smt_s2 smt_e2 smt_m2 elen2 mlen2,
                          eval_fp_exp fe2 s0 (SMTLIBfp.ieee754_fp smt_s2 smt_e2 smt_m2) elen2 mlen2 ->
                            (elen1 = wb_elen1 /\
                            mlen1 = wb_mlen1 /\
                            smt_s1 = (QFBV.eval_exp pack_s1 s1) /\ 
                            smt_e1 = (QFBV.eval_exp pack_e1 s1) /\ 
                            smt_m1 = (QFBV.eval_exp pack_m1 s1)) /\ 
                            (elen2 = wb_elen2 /\
                            mlen2 = wb_mlen2 /\
                            smt_s2 = (QFBV.eval_exp pack_s2 s2) /\ 
                            smt_e2 = (QFBV.eval_exp pack_e2 s2) /\ 
                            smt_m2 = (QFBV.eval_exp pack_m2 s2))) -> 
    forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
      Fq2bvq.well_formed_fp_bexp (Fq2bvq.FBbinop Fq2bvq.FBleq fe1 fe2) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' b,
              valid_gen_var gen_var ->
                (te', g', es', b) = word_blast_bexp gen_var g es te (Fq2bvq.FBbinop Fq2bvq.FBleq fe1 fe2) ->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && QFBV.well_formed_bexp b te' ->
                    conformed_bexps es' s' te' && conform_bexp b s' te' ->
                    eval_bexps es' s' ->
                      forall smt_b, eval_fp_bexp (Fq2bvq.FBbinop Fq2bvq.FBleq fe1 fe2) s smt_b ->
                        smt_b = QFBV.eval_bexp b s'.
Proof.
Admitted.

Lemma word_blasting_fp_bexp_semantics_equivalence_geq :
  forall fe1 fe2: Fq2bvq.fp_exp,
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_exp fe1 te0 ->
      Fq2bvq.well_formed_fp_exp fe2 te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1,
            valid_gen_var gen_var ->
              (te1, g1, es1, ubf1, wb_elen1, wb_mlen1) = word_blast_exp gen_var g0 es0 te0 fe1 ->
                forall s1 : SSAStore.t,
                  well_formed_bexps es1 te1 && Fq2bvq.well_formed_unpackedbf ubf1 te1 ->
                  conformed_bexps es1 s1 te1 && Fq2bvq.conform_unpackedbf ubf1 s1 te1 ->
                  eval_bexps es1 s1 ->
                    forall pack_s1 pack_e1 pack_m1, 
                      (pack_s1, pack_e1, pack_m1) = pack wb_mlen1 wb_elen1 ubf1 ->
                        forall smt_s1 smt_e1 smt_m1 elen1 mlen1,
                          eval_fp_exp fe1 s0 (SMTLIBfp.ieee754_fp smt_s1 smt_e1 smt_m1) elen1 mlen1 ->
          forall g2 te2 es2 ubf2 wb_elen2 wb_mlen2,
              (te2, g2, es2, ubf2, wb_elen2, wb_mlen2) = word_blast_exp gen_var g1 es1 te1 fe2 ->
                forall s2 : SSAStore.t,
                  well_formed_bexps es2 te2 && Fq2bvq.well_formed_unpackedbf ubf2 te2 ->
                  conformed_bexps es2 s2 te2 && Fq2bvq.conform_unpackedbf ubf2 s2 te2 ->
                  eval_bexps es2 s2 ->
                    forall pack_s2 pack_e2 pack_m2, 
                      (pack_s2, pack_e2, pack_m2) = pack wb_mlen2 wb_elen2 ubf2 ->
                        forall smt_s2 smt_e2 smt_m2 elen2 mlen2,
                          eval_fp_exp fe2 s0 (SMTLIBfp.ieee754_fp smt_s2 smt_e2 smt_m2) elen2 mlen2 ->
                            (elen1 = wb_elen1 /\
                            mlen1 = wb_mlen1 /\
                            smt_s1 = (QFBV.eval_exp pack_s1 s1) /\ 
                            smt_e1 = (QFBV.eval_exp pack_e1 s1) /\ 
                            smt_m1 = (QFBV.eval_exp pack_m1 s1)) /\ 
                            (elen2 = wb_elen2 /\
                            mlen2 = wb_mlen2 /\
                            smt_s2 = (QFBV.eval_exp pack_s2 s2) /\ 
                            smt_e2 = (QFBV.eval_exp pack_e2 s2) /\ 
                            smt_m2 = (QFBV.eval_exp pack_m2 s2))) -> 
    forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
      Fq2bvq.well_formed_fp_bexp (Fq2bvq.FBbinop Fq2bvq.FBgeq fe1 fe2) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' b,
              valid_gen_var gen_var ->
                (te', g', es', b) = word_blast_bexp gen_var g es te (Fq2bvq.FBbinop Fq2bvq.FBgeq fe1 fe2) ->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && QFBV.well_formed_bexp b te' ->
                    conformed_bexps es' s' te' && conform_bexp b s' te' ->
                    eval_bexps es' s' ->
                      forall smt_b, eval_fp_bexp (Fq2bvq.FBbinop Fq2bvq.FBgeq fe1 fe2) s smt_b ->
                        smt_b = QFBV.eval_bexp b s'.
Proof.
Admitted.

Lemma word_blasting_fp_bexp_semantics_equivalence_binop :
  forall (op : Fq2bvq.fbbinop) (fe1 fe2 : Fq2bvq.fp_exp),
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_exp fe1 te0 ->
      Fq2bvq.well_formed_fp_exp fe2 te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1,
            valid_gen_var gen_var ->
              (te1, g1, es1, ubf1, wb_elen1, wb_mlen1) = word_blast_exp gen_var g0 es0 te0 fe1 ->
                forall s1 : SSAStore.t,
                  well_formed_bexps es1 te1 && Fq2bvq.well_formed_unpackedbf ubf1 te1 ->
                  conformed_bexps es1 s1 te1 && Fq2bvq.conform_unpackedbf ubf1 s1 te1 ->
                  eval_bexps es1 s1 ->
                    forall pack_s1 pack_e1 pack_m1, 
                      (pack_s1, pack_e1, pack_m1) = pack wb_mlen1 wb_elen1 ubf1 ->
                        forall smt_s1 smt_e1 smt_m1 elen1 mlen1,
                          eval_fp_exp fe1 s0 (SMTLIBfp.ieee754_fp smt_s1 smt_e1 smt_m1) elen1 mlen1 ->
          forall g2 te2 es2 ubf2 wb_elen2 wb_mlen2,
              (te2, g2, es2, ubf2, wb_elen2, wb_mlen2) = word_blast_exp gen_var g1 es1 te1 fe2 ->
                forall s2 : SSAStore.t,
                  well_formed_bexps es2 te2 && Fq2bvq.well_formed_unpackedbf ubf2 te2 ->
                  conformed_bexps es2 s2 te2 && Fq2bvq.conform_unpackedbf ubf2 s2 te2 ->
                  eval_bexps es2 s2 ->
                    forall pack_s2 pack_e2 pack_m2, 
                      (pack_s2, pack_e2, pack_m2) = pack wb_mlen2 wb_elen2 ubf2 ->
                        forall smt_s2 smt_e2 smt_m2 elen2 mlen2,
                          eval_fp_exp fe2 s0 (SMTLIBfp.ieee754_fp smt_s2 smt_e2 smt_m2) elen2 mlen2 ->
                            (elen1 = wb_elen1 /\
                            mlen1 = wb_mlen1 /\
                            smt_s1 = (QFBV.eval_exp pack_s1 s1) /\ 
                            smt_e1 = (QFBV.eval_exp pack_e1 s1) /\ 
                            smt_m1 = (QFBV.eval_exp pack_m1 s1)) /\ 
                            (elen2 = wb_elen2 /\
                            mlen2 = wb_mlen2 /\
                            smt_s2 = (QFBV.eval_exp pack_s2 s2) /\ 
                            smt_e2 = (QFBV.eval_exp pack_e2 s2) /\ 
                            smt_m2 = (QFBV.eval_exp pack_m2 s2))) -> 
    forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
      Fq2bvq.well_formed_fp_bexp (Fq2bvq.FBbinop op fe1 fe2) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' b,
              valid_gen_var gen_var ->
                (te', g', es', b) = word_blast_bexp gen_var g es te (Fq2bvq.FBbinop op fe1 fe2) ->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && QFBV.well_formed_bexp b te' ->
                    conformed_bexps es' s' te' && conform_bexp b s' te' ->
                    eval_bexps es' s' ->
                      forall smt_b, eval_fp_bexp (Fq2bvq.FBbinop op fe1 fe2) s smt_b ->
                        smt_b = QFBV.eval_bexp b s'.
Proof.
Admitted.

End BBinop.

Lemma word_blasting_fp_bexp_semantics_equivalence_lneg :
  forall fb : Fq2bvq.fp_bexp,
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_bexp fb te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 b1,
            valid_gen_var gen_var ->
              (te1, g1, es1, b1) = word_blast_bexp gen_var g0 es0 te0 fb ->
                forall s1 : SSAStore.t,
                  well_formed_bexps es1 te1 && QFBV.well_formed_bexp b1 te1 ->
                  conformed_bexps es1 s1 te1 && conform_bexp b1 s1 te1 ->
                  eval_bexps es1 s1 ->
                    forall smt_b1, eval_fp_bexp fb s0 smt_b1 ->
                      smt_b1 = QFBV.eval_bexp b1 s1) ->
    forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
      Fq2bvq.well_formed_fp_bexp (Fq2bvq.FBlneg fb) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' b,
              valid_gen_var gen_var ->
                (te', g', es', b) = word_blast_bexp gen_var g es te (Fq2bvq.FBlneg fb) ->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && QFBV.well_formed_bexp b te' ->
                    conformed_bexps es' s' te' && conform_bexp b s' te' ->
                    eval_bexps es' s' ->
                      forall smt_b, eval_fp_bexp (Fq2bvq.FBlneg fb) s smt_b ->
                        smt_b = QFBV.eval_bexp b s'.
Proof.
  move => fb IH /= te s es g Hwf Heswf Hescf Hes gen_var g' te' es' b Hgv wb s' Hwbwf Hwbcf Hes' smt_b Hsmt.
  case Hwb1: (word_blast_bexp gen_var g es te fb) => [[[te1 g1] es1] b1].
  rewrite Hwb1 in wb. inversion wb. symmetry in Hwb1.
  move : (word_blasting_fp_bexp_is_wellformed fb te es g Hwf Heswf gen_var g1 te1 es1 b1 Hgv Hwb1) => Hwbwf1.
  move : (word_blasting_fp_bexp_is_conformed fb te s es g Hwf Heswf Hescf gen_var g1 te1 es1 b1 Hgv Hwb1 Hwbwf1) => Hwbcf1.
  destruct Hwbcf1 as [s1 Hwbcf1].
  move : (word_blasting_fp_bexp_eval_es fb te s es g Hwf Heswf Hescf Hes gen_var g1 te1 es1 b1 Hgv Hwb1 s1 Hwbwf1 Hwbcf1) => Hes1.
  specialize (IH te s es g Hwf Heswf Hescf Hes gen_var g1 te1 es1 b1 Hgv Hwb1 s1 Hwbwf1 Hwbcf1 Hes1).
  inversion Hsmt. subst. specialize (IH b0 H4). 
  assert (Hb1 : QFBV.eval_bexp b1 s' = QFBV.eval_bexp b1 s1). admit.
  simpl. rewrite IH Hb1 //.
Admitted.

Lemma word_blasting_fp_bexp_semantics_equivalence_conj :
  forall fb1 fb2: Fq2bvq.fp_bexp,
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_bexp fb1 te0 ->
      Fq2bvq.well_formed_fp_bexp fb2 te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 b1,
            valid_gen_var gen_var ->
              (te1, g1, es1, b1) = word_blast_bexp gen_var g0 es0 te0 fb1 ->
                forall s1 : SSAStore.t,
                  well_formed_bexps es1 te1 && QFBV.well_formed_bexp b1 te1 ->
                  conformed_bexps es1 s1 te1 && conform_bexp b1 s1 te1 ->
                  eval_bexps es1 s1 ->
                    forall smt_b1, eval_fp_bexp fb1 s0 smt_b1 ->
          forall g2 te2 es2 b2,
            (te2, g2, es2, b2) = word_blast_bexp gen_var g1 es1 te1 fb2 ->
              forall s2 : SSAStore.t,
                well_formed_bexps es2 te2 && QFBV.well_formed_bexp b2 te2 ->
                conformed_bexps es2 s2 te2 && conform_bexp b2 s2 te2 ->
                eval_bexps es2 s2 ->
                  forall smt_b2, eval_fp_bexp fb2 s0 smt_b2 ->
                    smt_b1 = (QFBV.eval_bexp b1 s1) /\
                    smt_b2 = (QFBV.eval_bexp b2 s2)) ->
    forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
      Fq2bvq.well_formed_fp_bexp (Fq2bvq.FBconj fb1 fb2) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' b,
              valid_gen_var gen_var ->
                (te', g', es', b) = word_blast_bexp gen_var g es te (Fq2bvq.FBconj fb1 fb2) ->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && QFBV.well_formed_bexp b te' ->
                    conformed_bexps es' s' te' && conform_bexp b s' te' ->
                    eval_bexps es' s' ->
                      forall smt_b, eval_fp_bexp (Fq2bvq.FBconj fb1 fb2) s smt_b ->
                        smt_b = QFBV.eval_bexp b s'.
Proof.
  move => fb1 fb2 IH /= te s es g Hwf Heswf Hescf Hes gen_var g' te' es' b Hgv wb s' Hwbwf Hwbcf Hes' smt_b Hsmt.
  case Hwb1: (word_blast_bexp gen_var g es te fb1) => [[[te1 g1] es1] b1].
  case Hwb2: (word_blast_bexp gen_var g1 es1 te1 fb2) => [[[te2 g2] es2] b2].
  rewrite Hwb1 Hwb2 in wb. inversion wb. symmetry in Hwb1. symmetry in Hwb2. simpl.
  apply Bools.and_true in Hwf. move : Hwf => [Hwf1 Hwf2].
  
  move : (word_blasting_fp_bexp_is_wellformed fb1 te es g Hwf1 Heswf gen_var g1 te1 es1 b1 Hgv Hwb1) => Hwbwf1.
  move : (word_blasting_fp_bexp_is_conformed fb1 te s es g Hwf1 Heswf Hescf gen_var g1 te1 es1 b1 Hgv Hwb1 Hwbwf1) => Hwbcf1.
  destruct Hwbcf1 as [s1 Hwbcf1].
  move : (word_blasting_fp_bexp_eval_es fb1 te s es g Hwf1 Heswf Hescf Hes gen_var g1 te1 es1 b1 Hgv Hwb1 s1 Hwbwf1 Hwbcf1) => Hes1.
  specialize (IH te s es g Hwf1 Hwf2 Heswf Hescf Hes gen_var g1 te1 es1 b1 Hgv Hwb1 s1 Hwbwf1 Hwbcf1 Hes1).
  inversion Hsmt. subst. specialize (IH b0 H5).
  
  assert (Hwf2' : Fq2bvq.well_formed_fp_bexp fb2 te1). admit.
  apply Bools.and_true in Hwbwf1. move : Hwbwf1 => [Heswf1 Hbwf1].
  move : (word_blasting_fp_bexp_is_wellformed fb2 te1 es1 g1 Hwf2' Heswf1 gen_var g2 te2 es2 b2 Hgv Hwb2) => Hwbwf2.
  apply Bools.and_true in Hwbcf1. move : Hwbcf1 => [Hescf1 Hbcf1].
  move : (word_blasting_fp_bexp_is_conformed fb2 te1 s1 es1 g1 Hwf2' Heswf1 Hescf1 gen_var g2 te2 es2 b2 Hgv Hwb2 Hwbwf2) => Hwbcf2.
  destruct Hwbcf2 as [s2 Hwbcf2].
  move : (word_blasting_fp_bexp_eval_es fb2 te1 s1 es1 g1 Hwf2' Heswf1 Hescf1 Hes1 gen_var g2 te2 es2 b2 Hgv Hwb2 s2 Hwbwf2 Hwbcf2) => Hes2.
  specialize (IH g2 te2 es2 b2 Hwb2 s2 Hwbwf2 Hwbcf2 Hes2 b3 H8).
  move : IH => [Hb1 Hb2]. 
  assert (Hb1' : QFBV.eval_bexp b1 s' = QFBV.eval_bexp b1 s1). admit.
  assert (Hb2' : QFBV.eval_bexp b2 s' = QFBV.eval_bexp b2 s2). admit.
  rewrite Hb1 Hb2 Hb1' Hb2' //.
Admitted.

Lemma word_blasting_fp_bexp_semantics_equivalence_disj :
  forall fb1 fb2: Fq2bvq.fp_bexp,
    (forall (te0 : SSATE.env) (s0 : SSAStore.t) (es0 : seq QFBV.bexp) (g0 : nat),
      Fq2bvq.well_formed_fp_bexp fb1 te0 ->
      Fq2bvq.well_formed_fp_bexp fb2 te0 ->
        well_formed_bexps es0 te0 ->
        conformed_bexps es0 s0 te0 ->
        eval_bexps es0 s0 ->
          forall gen_var g1 te1 es1 b1,
            valid_gen_var gen_var ->
              (te1, g1, es1, b1) = word_blast_bexp gen_var g0 es0 te0 fb1 ->
                forall s1 : SSAStore.t,
                  well_formed_bexps es1 te1 && QFBV.well_formed_bexp b1 te1 ->
                  conformed_bexps es1 s1 te1 && conform_bexp b1 s1 te1 ->
                  eval_bexps es1 s1 ->
                    forall smt_b1, eval_fp_bexp fb1 s0 smt_b1 ->
          forall g2 te2 es2 b2,
            (te2, g2, es2, b2) = word_blast_bexp gen_var g1 es1 te1 fb2 ->
              forall s2 : SSAStore.t,
                well_formed_bexps es2 te2 && QFBV.well_formed_bexp b2 te2 ->
                conformed_bexps es2 s2 te2 && conform_bexp b2 s2 te2 ->
                eval_bexps es2 s2 ->
                  forall smt_b2, eval_fp_bexp fb2 s0 smt_b2 ->
                    smt_b1 = (QFBV.eval_bexp b1 s1) /\
                    smt_b2 = (QFBV.eval_bexp b2 s2)) ->
    forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
      Fq2bvq.well_formed_fp_bexp (Fq2bvq.FBdisj fb1 fb2) te ->
          well_formed_bexps es te ->
          conformed_bexps es s te ->
          eval_bexps es s ->
            forall gen_var g' te' es' b,
              valid_gen_var gen_var ->
                (te', g', es', b) = word_blast_bexp gen_var g es te (Fq2bvq.FBdisj fb1 fb2) ->
                  forall s' : SSAStore.t,
                    well_formed_bexps es' te' && QFBV.well_formed_bexp b te' ->
                    conformed_bexps es' s' te' && conform_bexp b s' te' ->
                    eval_bexps es' s' ->
                      forall smt_b, eval_fp_bexp (Fq2bvq.FBdisj fb1 fb2) s smt_b ->
                        smt_b = QFBV.eval_bexp b s'.
Proof.
  move => fb1 fb2 IH /= te s es g Hwf Heswf Hescf Hes gen_var g' te' es' b Hgv wb s' Hwbwf Hwbcf Hes' smt_b Hsmt.
  case Hwb1: (word_blast_bexp gen_var g es te fb1) => [[[te1 g1] es1] b1].
  case Hwb2: (word_blast_bexp gen_var g1 es1 te1 fb2) => [[[te2 g2] es2] b2].
  rewrite Hwb1 Hwb2 in wb. inversion wb. symmetry in Hwb1. symmetry in Hwb2. simpl.
  apply Bools.and_true in Hwf. move : Hwf => [Hwf1 Hwf2].
  
  move : (word_blasting_fp_bexp_is_wellformed fb1 te es g Hwf1 Heswf gen_var g1 te1 es1 b1 Hgv Hwb1) => Hwbwf1.
  move : (word_blasting_fp_bexp_is_conformed fb1 te s es g Hwf1 Heswf Hescf gen_var g1 te1 es1 b1 Hgv Hwb1 Hwbwf1) => Hwbcf1.
  destruct Hwbcf1 as [s1 Hwbcf1].
  move : (word_blasting_fp_bexp_eval_es fb1 te s es g Hwf1 Heswf Hescf Hes gen_var g1 te1 es1 b1 Hgv Hwb1 s1 Hwbwf1 Hwbcf1) => Hes1.
  specialize (IH te s es g Hwf1 Hwf2 Heswf Hescf Hes gen_var g1 te1 es1 b1 Hgv Hwb1 s1 Hwbwf1 Hwbcf1 Hes1).
  inversion Hsmt. subst. specialize (IH b0 H5).
  
  assert (Hwf2' : Fq2bvq.well_formed_fp_bexp fb2 te1). admit.
  apply Bools.and_true in Hwbwf1. move : Hwbwf1 => [Heswf1 Hbwf1].
  move : (word_blasting_fp_bexp_is_wellformed fb2 te1 es1 g1 Hwf2' Heswf1 gen_var g2 te2 es2 b2 Hgv Hwb2) => Hwbwf2.
  apply Bools.and_true in Hwbcf1. move : Hwbcf1 => [Hescf1 Hbcf1].
  move : (word_blasting_fp_bexp_is_conformed fb2 te1 s1 es1 g1 Hwf2' Heswf1 Hescf1 gen_var g2 te2 es2 b2 Hgv Hwb2 Hwbwf2) => Hwbcf2.
  destruct Hwbcf2 as [s2 Hwbcf2].
  move : (word_blasting_fp_bexp_eval_es fb2 te1 s1 es1 g1 Hwf2' Heswf1 Hescf1 Hes1 gen_var g2 te2 es2 b2 Hgv Hwb2 s2 Hwbwf2 Hwbcf2) => Hes2.
  specialize (IH g2 te2 es2 b2 Hwb2 s2 Hwbwf2 Hwbcf2 Hes2 b3 H8).
  move : IH => [Hb1 Hb2]. 
  assert (Hb1' : QFBV.eval_bexp b1 s' = QFBV.eval_bexp b1 s1). admit.
  assert (Hb2' : QFBV.eval_bexp b2 s' = QFBV.eval_bexp b2 s2). admit.
  rewrite Hb1 Hb2 Hb1' Hb2' //.
Admitted.

Theorem word_blasting_fp_exp_semantics_equivalence :
  forall (fe: Fq2bvq.fp_exp),
    forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
      Fq2bvq.well_formed_fp_exp fe te ->
        well_formed_bexps es te ->
        conformed_bexps es s te ->
        eval_bexps es s ->
          forall gen_var g' te' es' ubf wb_elen wb_mlen,
            valid_gen_var gen_var ->
              (te', g', es', ubf, wb_elen, wb_mlen) = word_blast_exp gen_var g es te fe ->
                forall s' : SSAStore.t,
                  well_formed_bexps es' te' && Fq2bvq.well_formed_unpackedbf ubf te' ->
                  conformed_bexps es' s' te' && Fq2bvq.conform_unpackedbf ubf s' te' ->
                  eval_bexps es' s' ->
                    forall pack_s pack_e pack_m, 
                      (pack_s, pack_e, pack_m) = pack wb_mlen wb_elen ubf ->
                        (forall smt_s smt_e smt_m elen mlen,
                          eval_fp_exp fe s (SMTLIBfp.ieee754_fp smt_s smt_e smt_m) elen mlen ->
                          elen = wb_elen /\
                          mlen = wb_mlen /\
                          smt_s = (QFBV.eval_exp pack_s s') /\ 
                          smt_e = (QFBV.eval_exp pack_e s') /\ 
                          smt_m = (QFBV.eval_exp pack_m s'))
  with 
    word_blasting_fp_bexp_semantics_equivalence :
      forall (fb : Fq2bvq.fp_bexp),
        forall (te : SSATE.env) (s : SSAStore.t) (es : seq QFBV.bexp) (g : nat),
          Fq2bvq.well_formed_fp_bexp fb te ->
              well_formed_bexps es te ->
              conformed_bexps es s te ->
              eval_bexps es s ->
                forall gen_var g' te' es' b,
                  valid_gen_var gen_var ->
                    (te', g', es', b) = word_blast_bexp gen_var g es te fb ->
                      forall s' : SSAStore.t,
                        well_formed_bexps es' te' && QFBV.well_formed_bexp b te' ->
                        conformed_bexps es' s' te' && conform_bexp b s' te' ->
                        eval_bexps es' s' ->
                          forall smt_b, eval_fp_bexp fb s smt_b ->
                            smt_b = QFBV.eval_bexp b s'.
Proof.
  (* exp *)
  set IHe := word_blasting_fp_exp_semantics_equivalence.
  set IHb := word_blasting_fp_bexp_semantics_equivalence.
  case.
  + exact : word_blasting_fp_exp_semantics_equivalence_ieee754.
  + move => op fe. move: op fe (IHe fe).
    exact : word_blasting_fp_exp_semantics_equivalence_unop.
  + move => op rm fe. move: op rm fe (IHe fe).
    exact : word_blasting_fp_exp_semantics_equivalence_rmunop.
  + move => op fe1 fe2.
    move : (word_blasting_fp_exp_semantics_equivalence_binop op fe1 fe2) => IH.
    apply IH.
    move => te0 s0 es0 g0 Hwf1 Hwf2 Heswf Hescf Hes gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hvgr Hwb1 s1 Hwbwf1 Hwbcf1 Hes1 pack_s1 pack_e1 pack_m1 Hpack1 smt_s1 smt_e1 smt_m1 elen1 mlen1 Hsmt1.
    move => g2 te2 es2 ubf2 wb_elen2 wb_mlen2 Hwb2 s2 Hwbwf2 Hwbcf2 Hes2 pack_s2 pack_e2 pack_m2 Hpack2 smt_s2 smt_e2 smt_m2 elen2 mlen2 Hsmt2.
    move : (IHe fe1 te0 s0 es0 g0) => IHe1.
    move : (IHe fe2 te1 s1 es1 g1) => IHe2.
    specialize (IHe1 Hwf1 Heswf Hescf Hes gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hvgr Hwb1 s1 Hwbwf1 Hwbcf1 Hes1 pack_s1 pack_e1 pack_m1 Hpack1 smt_s1 smt_e1 smt_m1 elen1 mlen1 Hsmt1).
    apply Bools.and_true in Hwbwf1. move : Hwbwf1 => [Heswf1 Hubfwf1].
    apply Bools.and_true in Hwbcf1. move : Hwbcf1 => [Hescf1 Hubfcf1].
    
    assert (Hwf2' : Fq2bvq.well_formed_fp_exp fe2 te1). admit.
    assert (Hsmt2' : eval_fp_exp fe2 s1 (SMTLIBfp.ieee754_fp smt_s2 smt_e2 smt_m2) elen2 mlen2). admit.
    specialize (IHe2 Hwf2' Heswf1 Hescf1 Hes1 gen_var g2 te2 es2 ubf2 wb_elen2 wb_mlen2 Hvgr Hwb2 s2 Hwbwf2 Hwbcf2 Hes2 pack_s2 pack_e2 pack_m2 Hpack2 smt_s2 smt_e2 smt_m2 elen2 mlen2 Hsmt2').
    split. apply IHe1. apply IHe2.
  + move => rm op fe1 fe2.
    move : (word_blasting_fp_exp_semantics_equivalence_rmbinop rm op fe1 fe2) => IH.
    apply IH.
    move => te0 s0 es0 g0 Hwf1 Hwf2 Heswf Hescf Hes gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hvgr Hwb1 s1 Hwbwf1 Hwbcf1 Hes1 pack_s1 pack_e1 pack_m1 Hpack1 smt_s1 smt_e1 smt_m1 elen1 mlen1 Hsmt1.
    move => g2 te2 es2 ubf2 wb_elen2 wb_mlen2 Hwb2 s2 Hwbwf2 Hwbcf2 Hes2 pack_s2 pack_e2 pack_m2 Hpack2 smt_s2 smt_e2 smt_m2 elen2 mlen2 Hsmt2.
    move : (IHe fe1 te0 s0 es0 g0) => IHe1.
    move : (IHe fe2 te1 s1 es1 g1) => IHe2.
    specialize (IHe1 Hwf1 Heswf Hescf Hes gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hvgr Hwb1 s1 Hwbwf1 Hwbcf1 Hes1 pack_s1 pack_e1 pack_m1 Hpack1 smt_s1 smt_e1 smt_m1 elen1 mlen1 Hsmt1).
    apply Bools.and_true in Hwbwf1. move : Hwbwf1 => [Heswf1 Hubfwf1].
    apply Bools.and_true in Hwbcf1. move : Hwbcf1 => [Hescf1 Hubfcf1].
    assert (Hwf2' : Fq2bvq.well_formed_fp_exp fe2 te1). admit.
    assert (Hsmt2' : eval_fp_exp fe2 s1 (SMTLIBfp.ieee754_fp smt_s2 smt_e2 smt_m2) elen2 mlen2). admit.
    specialize (IHe2 Hwf2' Heswf1 Hescf1 Hes1 gen_var g2 te2 es2 ubf2 wb_elen2 wb_mlen2 Hvgr Hwb2 s2 Hwbwf2 Hwbcf2 Hes2 pack_s2 pack_e2 pack_m2 Hpack2 smt_s2 smt_e2 smt_m2 elen2 mlen2 Hsmt2').
    split. apply IHe1. apply IHe2.
  + move => rm op fe1 fe2 fe3.
    move : (word_blasting_fp_exp_semantics_equivalence_rmtriop rm op fe1 fe2 fe3) => IH.
    apply IH.
    move => te0 s0 es0 g0 Hwf1 Hwf2 Hwf3 Heswf Hescf Hes gen_var. 
    move => g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hvgr Hwb1 s1 Hwbwf1 Hwbcf1 Hes1 pack_s1 pack_e1 pack_m1 Hpack1 smt_s1 smt_e1 smt_m1 elen1 mlen1 Hsmt1.
    move => g2 te2 es2 ubf2 wb_elen2 wb_mlen2 Hwb2 s2 Hwbwf2 Hwbcf2 Hes2 pack_s2 pack_e2 pack_m2 Hpack2 smt_s2 smt_e2 smt_m2 elen2 mlen2 Hsmt2.
    move => g3 te3 es3 ubf3 wb_elen3 wb_mlen3 Hwb3 s3 Hwbwf3 Hwbcf3 Hes3 pack_s3 pack_e3 pack_m3 Hpack3 smt_s3 smt_e3 smt_m3 elen3 mlen3 Hsmt3.
    move : (IHe fe1 te0 s0 es0 g0) => IHe1.
    move : (IHe fe2 te1 s1 es1 g1) => IHe2.
    move : (IHe fe3 te2 s2 es2 g2) => IHe3.
    specialize (IHe1 Hwf1 Heswf Hescf Hes gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hvgr Hwb1 s1 Hwbwf1 Hwbcf1 Hes1 pack_s1 pack_e1 pack_m1 Hpack1 smt_s1 smt_e1 smt_m1 elen1 mlen1 Hsmt1).
    apply Bools.and_true in Hwbwf1. move : Hwbwf1 => [Heswf1 Hubfwf1].
    apply Bools.and_true in Hwbcf1. move : Hwbcf1 => [Hescf1 Hubfcf1].
    assert (Hwf2' : Fq2bvq.well_formed_fp_exp fe2 te1). admit.
    assert (Hsmt2' : eval_fp_exp fe2 s1 (SMTLIBfp.ieee754_fp smt_s2 smt_e2 smt_m2) elen2 mlen2). admit.
    specialize (IHe2 Hwf2' Heswf1 Hescf1 Hes1 gen_var g2 te2 es2 ubf2 wb_elen2 wb_mlen2 Hvgr Hwb2 s2 Hwbwf2 Hwbcf2 Hes2 pack_s2 pack_e2 pack_m2 Hpack2 smt_s2 smt_e2 smt_m2 elen2 mlen2 Hsmt2').
    apply Bools.and_true in Hwbwf2. move : Hwbwf2 => [Heswf2 Hubfwf2].
    apply Bools.and_true in Hwbcf2. move : Hwbcf2 => [Hescf2 Hubfcf2].
    assert (Hwf3' : Fq2bvq.well_formed_fp_exp fe3 te2). admit.
    assert (Hsmt3' : eval_fp_exp fe3 s2 (SMTLIBfp.ieee754_fp smt_s3 smt_e3 smt_m3) elen3 mlen3). admit.
    specialize (IHe3 Hwf3' Heswf2 Hescf2 Hes2 gen_var g3 te3 es3 ubf3 wb_elen3 wb_mlen3 Hvgr Hwb3 s3 Hwbwf3 Hwbcf3 Hes3 pack_s3 pack_e3 pack_m3 Hpack3 smt_s3 smt_e3 smt_m3 elen3 mlen3 Hsmt3').
    split. apply IHe1. split. apply IHe2. apply IHe3.
  + move => rm fe telen tmlen. move: rm fe telen tmlen (IHe fe).
    exact : word_blasting_fp_exp_semantics_equivalence_ofbf.
  + exact : word_blasting_fp_exp_semantics_equivalence_ofbv.
  + exact : word_blasting_fp_exp_semantics_equivalence_ofsbv.
  + exact : word_blasting_fp_exp_semantics_equivalence_ofubv.
  + move => fb1 fe2 fe3.
    move : (word_blasting_fp_exp_semantics_equivalence_ite fb1 fe2 fe3) => IH.
    apply IH.
    move => te0 s0 es0 g0 Hwf1 Hwf2 Hwf3 Heswf Hescf Hes gen_var. 
    move => g1 te1 es1 b1 Hvgr Hwb1 s1 Hwbwf1 Hwbcf1 Hes1 smt_b1 Hsmt1.
    move => g2 te2 es2 ubf2 wb_elen2 wb_mlen2 Hwb2 s2 Hwbwf2 Hwbcf2 Hes2 pack_s2 pack_e2 pack_m2 Hpack2 smt_s2 smt_e2 smt_m2 elen2 mlen2 Hsmt2.
    move => g3 te3 es3 ubf3 wb_elen3 wb_mlen3 Hwb3 s3 Hwbwf3 Hwbcf3 Hes3 pack_s3 pack_e3 pack_m3 Hpack3 smt_s3 smt_e3 smt_m3 elen3 mlen3 Hsmt3.
    move : (IHb fb1 te0 s0 es0 g0) => IHb1.
    move : (IHe fe2 te1 s1 es1 g1) => IHe2.
    move : (IHe fe3 te2 s2 es2 g2) => IHe3.
    specialize (IHb1 Hwf1 Heswf Hescf Hes gen_var g1 te1 es1 b1 Hvgr Hwb1 s1 Hwbwf1 Hwbcf1 Hes1 smt_b1 Hsmt1).
    apply Bools.and_true in Hwbwf1. move : Hwbwf1 => [Heswf1 Hubfwf1].
    apply Bools.and_true in Hwbcf1. move : Hwbcf1 => [Hescf1 Hubfcf1].
    assert (Hwf2' : Fq2bvq.well_formed_fp_exp fe2 te1). admit.
    assert (Hsmt2' : eval_fp_exp fe2 s1 (SMTLIBfp.ieee754_fp smt_s2 smt_e2 smt_m2) elen2 mlen2). admit.
    specialize (IHe2 Hwf2' Heswf1 Hescf1 Hes1 gen_var g2 te2 es2 ubf2 wb_elen2 wb_mlen2 Hvgr Hwb2 s2 Hwbwf2 Hwbcf2 Hes2 pack_s2 pack_e2 pack_m2 Hpack2 smt_s2 smt_e2 smt_m2 elen2 mlen2 Hsmt2').
    apply Bools.and_true in Hwbwf2. move : Hwbwf2 => [Heswf2 Hubfwf2].
    apply Bools.and_true in Hwbcf2. move : Hwbcf2 => [Hescf2 Hubfcf2].
    assert (Hwf3' : Fq2bvq.well_formed_fp_exp fe3 te2). admit.
    assert (Hsmt3' : eval_fp_exp fe3 s2 (SMTLIBfp.ieee754_fp smt_s3 smt_e3 smt_m3) elen3 mlen3). admit.
    specialize (IHe3 Hwf3' Heswf2 Hescf2 Hes2 gen_var g3 te3 es3 ubf3 wb_elen3 wb_mlen3 Hvgr Hwb3 s3 Hwbwf3 Hwbcf3 Hes3 pack_s3 pack_e3 pack_m3 Hpack3 smt_s3 smt_e3 smt_m3 elen3 mlen3 Hsmt3').
    split. apply IHb1. split. apply IHe2. apply IHe3.
  (* bexp *)
  set IHe := word_blasting_fp_exp_semantics_equivalence.
  set IHb := word_blasting_fp_bexp_semantics_equivalence.
  case.
  + exact : word_blasting_fp_bexp_semantics_equivalence_false.
  + exact : word_blasting_fp_bexp_semantics_equivalence_true.
  + exact : word_blasting_fp_bexp_semantics_equivalence_boolvar.
  + move => fe1 fe2.
    move : (word_blasting_fp_bexp_semantics_equivalence_bveq fe1 fe2) => IH.
    apply IH.
    move => te0 s0 es0 g0 Hwf1 Hwf2 Heswf Hescf Hes gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hvgr Hwb1 s1 Hwbwf1 Hwbcf1 Hes1 pack_s1 pack_e1 pack_m1 Hpack1 smt_s1 smt_e1 smt_m1 elen1 mlen1 Hsmt1.
    move => g2 te2 es2 ubf2 wb_elen2 wb_mlen2 Hwb2 s2 Hwbwf2 Hwbcf2 Hes2 pack_s2 pack_e2 pack_m2 Hpack2 smt_s2 smt_e2 smt_m2 elen2 mlen2 Hsmt2.
    move : (IHe fe1 te0 s0 es0 g0) => IHe1.
    move : (IHe fe2 te1 s1 es1 g1) => IHe2.
    specialize (IHe1 Hwf1 Heswf Hescf Hes gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hvgr Hwb1 s1 Hwbwf1 Hwbcf1 Hes1 pack_s1 pack_e1 pack_m1 Hpack1 smt_s1 smt_e1 smt_m1 elen1 mlen1 Hsmt1).
    apply Bools.and_true in Hwbwf1. move : Hwbwf1 => [Heswf1 Hubfwf1].
    apply Bools.and_true in Hwbcf1. move : Hwbcf1 => [Hescf1 Hubfcf1].
    assert (Hwf2' : Fq2bvq.well_formed_fp_exp fe2 te1). admit.
    assert (Hsmt2' : eval_fp_exp fe2 s1 (SMTLIBfp.ieee754_fp smt_s2 smt_e2 smt_m2) elen2 mlen2). admit.
    specialize (IHe2 Hwf2' Heswf1 Hescf1 Hes1 gen_var g2 te2 es2 ubf2 wb_elen2 wb_mlen2 Hvgr Hwb2 s2 Hwbwf2 Hwbcf2 Hes2 pack_s2 pack_e2 pack_m2 Hpack2 smt_s2 smt_e2 smt_m2 elen2 mlen2 Hsmt2').
    split. apply IHe1. apply IHe2.
  + move => op fe. move: op fe (IHe fe).
    exact : word_blasting_fp_bexp_semantics_equivalence_unop.
  + move => op fe1 fe2.
    move : (word_blasting_fp_bexp_semantics_equivalence_binop op fe1 fe2) => IH.
    apply IH.
    move => te0 s0 es0 g0 Hwf1 Hwf2 Heswf Hescf Hes gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hvgr Hwb1 s1 Hwbwf1 Hwbcf1 Hes1 pack_s1 pack_e1 pack_m1 Hpack1 smt_s1 smt_e1 smt_m1 elen1 mlen1 Hsmt1.
    move => g2 te2 es2 ubf2 wb_elen2 wb_mlen2 Hwb2 s2 Hwbwf2 Hwbcf2 Hes2 pack_s2 pack_e2 pack_m2 Hpack2 smt_s2 smt_e2 smt_m2 elen2 mlen2 Hsmt2.
    move : (IHe fe1 te0 s0 es0 g0) => IHe1.
    move : (IHe fe2 te1 s1 es1 g1) => IHe2.
    specialize (IHe1 Hwf1 Heswf Hescf Hes gen_var g1 te1 es1 ubf1 wb_elen1 wb_mlen1 Hvgr Hwb1 s1 Hwbwf1 Hwbcf1 Hes1 pack_s1 pack_e1 pack_m1 Hpack1 smt_s1 smt_e1 smt_m1 elen1 mlen1 Hsmt1).
    apply Bools.and_true in Hwbwf1. move : Hwbwf1 => [Heswf1 Hubfwf1].
    apply Bools.and_true in Hwbcf1. move : Hwbcf1 => [Hescf1 Hubfcf1].
    
    assert (Hwf2' : Fq2bvq.well_formed_fp_exp fe2 te1). admit.
    assert (Hsmt2' : eval_fp_exp fe2 s1 (SMTLIBfp.ieee754_fp smt_s2 smt_e2 smt_m2) elen2 mlen2). admit.
    specialize (IHe2 Hwf2' Heswf1 Hescf1 Hes1 gen_var g2 te2 es2 ubf2 wb_elen2 wb_mlen2 Hvgr Hwb2 s2 Hwbwf2 Hwbcf2 Hes2 pack_s2 pack_e2 pack_m2 Hpack2 smt_s2 smt_e2 smt_m2 elen2 mlen2 Hsmt2').
    split. apply IHe1. apply IHe2.
  + move => fb. move : fb (IHb fb).
    exact : word_blasting_fp_bexp_semantics_equivalence_lneg.
  + move => fb1 fb2.
    move : (word_blasting_fp_bexp_semantics_equivalence_conj fb1 fb2) => IH.
    apply IH.
    move => te0 s0 es0 g0 Hwf1 Hwf2 Heswf Hescf Hes gen_var.
    move => g1 te1 es1 b1 Hvgr Hwb1 s1 Hwbwf1 Hwbcf1 Hes1 smt_b1 Hsmt1.
    move => g2 te2 es2 b2 Hwb2 s2 Hwbwf2 Hwbcf2 Hes2 smt_b2 Hsmt2.
    move : (IHb fb1 te0 s0 es0 g0) => IHb1.
    move : (IHb fb2 te1 s1 es1 g1) => IHb2.
    specialize (IHb1 Hwf1 Heswf Hescf Hes gen_var g1 te1 es1 b1 Hvgr Hwb1 s1 Hwbwf1 Hwbcf1 Hes1 smt_b1 Hsmt1).
    apply Bools.and_true in Hwbwf1. move : Hwbwf1 => [Heswf1 Hubfwf1].
    apply Bools.and_true in Hwbcf1. move : Hwbcf1 => [Hescf1 Hubfcf1].
    assert (Hwf2' : Fq2bvq.well_formed_fp_bexp fb2 te1). admit.
    assert (Hsmt2' : eval_fp_bexp fb2 s1 smt_b2). admit.
    specialize (IHb2 Hwf2' Heswf1 Hescf1 Hes1 gen_var g2 te2 es2 b2 Hvgr Hwb2 s2 Hwbwf2 Hwbcf2 Hes2 smt_b2 Hsmt2').
    split. apply IHb1. apply IHb2.
  + move => fb1 fb2.
    move : (word_blasting_fp_bexp_semantics_equivalence_disj fb1 fb2) => IH.
    apply IH.
    move => te0 s0 es0 g0 Hwf1 Hwf2 Heswf Hescf Hes gen_var.
    move => g1 te1 es1 b1 Hvgr Hwb1 s1 Hwbwf1 Hwbcf1 Hes1 smt_b1 Hsmt1.
    move => g2 te2 es2 b2 Hwb2 s2 Hwbwf2 Hwbcf2 Hes2 smt_b2 Hsmt2.
    move : (IHb fb1 te0 s0 es0 g0) => IHb1.
    move : (IHb fb2 te1 s1 es1 g1) => IHb2.
    specialize (IHb1 Hwf1 Heswf Hescf Hes gen_var g1 te1 es1 b1 Hvgr Hwb1 s1 Hwbwf1 Hwbcf1 Hes1 smt_b1 Hsmt1).
    apply Bools.and_true in Hwbwf1. move : Hwbwf1 => [Heswf1 Hubfwf1].
    apply Bools.and_true in Hwbcf1. move : Hwbcf1 => [Hescf1 Hubfcf1].
    assert (Hwf2' : Fq2bvq.well_formed_fp_bexp fb2 te1). admit.
    assert (Hsmt2' : eval_fp_bexp fb2 s1 smt_b2). admit.
    specialize (IHb2 Hwf2' Heswf1 Hescf1 Hes1 gen_var g2 te2 es2 b2 Hvgr Hwb2 s2 Hwbwf2 Hwbcf2 Hes2 smt_b2 Hsmt2').
    split. apply IHb1. apply IHb2.
Admitted.
