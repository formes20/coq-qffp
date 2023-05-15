From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From BitBlasting Require Import Typ TypEnv State AdhereConform.
From BitBlasting Require Import QFBV.

From ssrlib Require Import EqVar.
From WordBlasting Require Import fq2bvq WBMain .

Import QFBV.
Import Fq2bvq.

Definition well_formed_bexp_forseq te b := QFBV.well_formed_bexp b te.
Definition well_formed_bexps es te := all (well_formed_bexp_forseq te) es.

Inductive valid_gen_var : (nat -> (ssavar * nat)) -> Prop :=
  | NewVar : forall gen_var : (nat -> (ssavar * nat)), 
             (forall v v' g g', ~(g = g') -> v = (gen_var g).1 -> v' = (gen_var g').1 -> ~(v = v')) ->
             forall g g', g' = (gen_var g).2 -> g' = g + 1 -> 
              valid_gen_var gen_var.
              
Definition exp_constraint (e : QFBV.exp) : bool :=
  match e with
  | QFBV.Econst _ | QFBV.Evar _ => true
  | _ => false
  end.
  
(* TODO: add lemmas *)

Theorem word_blasting_fp_exp_is_wellformed :
  forall (fe: Fq2bvq.fp_exp),
    forall (te : SSATE.env) (es : seq QFBV.bexp) (g : nat),
      Fq2bvq.well_formed_fp_exp fe te ->
        well_formed_bexps es te ->
          forall gen_var g' te' es' ubf wb_elen wb_mlen,
            valid_gen_var gen_var ->
              (te', g', es', ubf, wb_elen, wb_mlen) = word_blast_exp gen_var g es te fe ->
                 well_formed_bexps es' te' && Fq2bvq.well_formed_unpackedbf ubf te'
  with 
    word_blasting_fp_bexp_is_wellformed :
      forall (fb : Fq2bvq.fp_bexp),
        forall (te : SSATE.env) (es : seq QFBV.bexp) (g : nat),
          Fq2bvq.well_formed_fp_bexp fb te ->
              well_formed_bexps es te ->
                forall gen_var g' te' es' b,
                  valid_gen_var gen_var ->
                    (te', g', es', b) = word_blast_bexp gen_var g es te fb ->
                        well_formed_bexps es' te' && QFBV.well_formed_bexp b te'.
Proof.
Admitted.
