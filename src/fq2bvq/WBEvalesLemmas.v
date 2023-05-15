From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From BitBlasting Require Import Typ TypEnv State AdhereConform.
From BitBlasting Require Import QFBV.

From ssrlib Require Import Var.
From WordBlasting Require Import fq2bvq WBMain WBWellformLemmas WBConformLemmas.

Import QFBV.
Import Fq2bvq.

Definition well_formed_bexp_forseq te b := QFBV.well_formed_bexp b te.
Definition well_formed_bexps es te := all (well_formed_bexp_forseq te) es.

Definition eval_bexp_forseq s b := QFBV.eval_bexp b s.
Definition eval_bexps es s := all (eval_bexp_forseq s) es.

Theorem word_blasting_fp_exp_eval_es :
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
                  eval_bexps es' s'
  with 
    word_blasting_fp_bexp_eval_es :
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
                        eval_bexps es' s'.
Proof.
Admitted.
