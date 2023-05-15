From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From Coq Require Import ZArith.
From nbits Require Import NBits.
From BitBlasting Require Import Typ TypEnv State AdhereConform.
From BitBlasting Require Import QFBV.

From WordBlasting Require Import WBPacking.

Import QFBV.

Module MakeFq2bvq.

  Inductive feunop : Set :=
  | FUabs
  | FUneg.
  
  Inductive fermunop : Set :=
  | FRUsqrt
  | FRUrti.
  
  Inductive febinop : Set :=
  | FBmax
  | FBmin
  | FBrem.
  
  Inductive fermbinop : Set :=
  | FRBadd
  | FRBsub
  | FRBmul
  | FRBdiv.
  
  Inductive fermtriop : Set :=
  | FRTfma.
  
  Inductive fbunop : Set :=
  | FUisInfinite
  | FUisZero
  | FUisNaN
  | FUisNormal
  | FUisSubnormal
  | FUisNegative
  | FUisPositive.
  
  Inductive fbbinop : Set := 
  | FBeq
  | FBlt
  | FBgt
  | FBleq
  | FBgeq.

  Inductive fp_exp : Type :=
    | FEieee754 : nat -> nat -> exp -> exp -> exp -> fp_exp
    | FEunop : feunop -> fp_exp -> fp_exp
    | FErmunop : fermunop -> exp -> fp_exp -> fp_exp
    | FEbinop : febinop -> fp_exp -> fp_exp -> fp_exp
    | FErmbinop : fermbinop -> exp -> fp_exp -> fp_exp -> fp_exp
    | FErmtriop : fermtriop -> exp -> fp_exp -> fp_exp -> fp_exp -> fp_exp
    | FEofbf : exp -> fp_exp -> nat -> nat -> fp_exp
    | FEofbv : exp -> nat -> nat -> nat -> fp_exp
    | FEofsbv : exp -> exp -> nat -> nat -> nat -> fp_exp
    | FEofubv : exp -> exp -> nat -> nat -> nat -> fp_exp
    | FEite : fp_bexp -> fp_exp -> fp_exp -> fp_exp
    with
    fp_bexp : Type :=
    | FBfalse : fp_bexp
    | FBtrue : fp_bexp
    | FBvar : exp -> fp_bexp
    | FBbveq : fp_exp -> fp_exp -> fp_bexp (* It's better to call it FBident *)
    | FBunop : fbunop -> fp_exp -> fp_bexp
    | FBbinop : fbbinop -> fp_exp -> fp_exp -> fp_bexp
    | FBlneg : fp_bexp -> fp_bexp
    | FBconj : fp_bexp -> fp_bexp -> fp_bexp
    | FBdisj : fp_bexp -> fp_bexp -> fp_bexp.

  Fixpoint fp_exp_format (fe : fp_exp) : nat * nat :=
    match fe with
    | FEieee754 elen mlen s e m  => (elen, mlen)
    | FEunop op fe  => fp_exp_format fe
    | FErmunop op rm fe => fp_exp_format fe
    | FEbinop op fe1 fe2 => fp_exp_format fe1
    | FErmbinop op rm fe1 fe2 => fp_exp_format fe1
    | FErmtriop op rm fe1 fe2 fe3 => fp_exp_format fe1
    | FEofbf rm fe telen tmlen => (telen, tmlen)
    | FEofbv e n telen tmlen => (telen, tmlen)
    | FEofsbv rm e n telen tmlen => (telen, tmlen)
    | FEofubv rm e n telen tmlen => (telen, tmlen)
    | FEite fb fe1 fe2 => fp_exp_format fe1
    end.

  Fixpoint well_formed_fp_exp (fe : fp_exp) (te : SSATE.env) : bool :=
    match fe with
    | FEieee754 elen mlen s e m => (elen > 1) && (mlen > 1) && (elen <= mlen) && ((exp_size s te) == 1) && ((exp_size e te) == elen) && ((exp_size m te) == mlen)
    | FEunop op fe => well_formed_fp_exp fe te
    | FErmunop op rm fe => ((exp_size rm te) == 3) && well_formed_fp_exp fe te && ((exp_size rm te) == 3)
    | FEbinop op fe1 fe2 =>  let (elen1, mlen1) := fp_exp_format fe1 in
                             let (elen2, mlen2) := fp_exp_format fe2 in
                              well_formed_fp_exp fe1 te && well_formed_fp_exp fe2 te &&
                              (elen1 > 1) && (mlen1 > 1) && (elen1 <= mlen1) &&
                              (elen1 == elen2) && (mlen1 == mlen2)
    | FErmbinop op rm fe1 fe2 => let (elen1, mlen1) := fp_exp_format fe1 in
                                 let (elen2, mlen2) := fp_exp_format fe2 in
                                  ((exp_size rm te) == 3) &&
                                  well_formed_fp_exp fe1 te && well_formed_fp_exp fe2 te &&
                                  (elen1 > 1) && (mlen1 > 1) && (elen1 <= mlen1) &&
                                  (elen1 == elen2) && (mlen1 == mlen2) && ((exp_size rm te) == 3)
    | FErmtriop op rm fe1 fe2 fe3 => let (elen1, mlen1) := fp_exp_format fe1 in
                                     let (elen2, mlen2) := fp_exp_format fe2 in
                                     let (elen3, mlen3) := fp_exp_format fe3 in
                                      ((exp_size rm te) == 3) &&
                                      well_formed_fp_exp fe1 te && well_formed_fp_exp fe2 te && well_formed_fp_exp fe3 te &&
                                      (elen1 > 1) && (mlen1 > 1) && (elen1 <= mlen1) &&
                                      (elen1 == elen2) && (mlen1 == mlen2) && (elen1 == elen3) && (mlen1 == mlen3) && ((exp_size rm te) == 3)
    | FEofbf rm fe telen tmlen => let (elen, mlen) := fp_exp_format fe in
                                    ((exp_size rm te) == 3) &&
                                    well_formed_fp_exp fe te &&
                                    (elen > 1) && (mlen > 1) && (elen <= mlen) &&
                                    (telen > 1) && (tmlen > 1) && (telen <= tmlen)
    | FEofbv e n telen tmlen => (telen > 1) && (tmlen > 1) && (telen <= tmlen) && (n == (telen + tmlen + 1)) && ((exp_size e te) == n)
    | FEofsbv rm e n telen tmlen => ((exp_size rm te) == 3) && 
                                    (n > 1) && ((exp_size e te) == n) && 
                                    (telen > 1) && (tmlen > 1) && (telen <= tmlen)
    | FEofubv rm e n telen tmlen => ((exp_size rm te) == 3) && 
                                    (n > 1) && ((exp_size e te) == n) && 
                                    (telen > 1) && (tmlen > 1) && (telen <= tmlen)
    | FEite fb fe1 fe2 => let (elen1, mlen1) := fp_exp_format fe1 in
                          let (elen2, mlen2) := fp_exp_format fe2 in
                            well_formed_fp_bexp fb te && well_formed_fp_exp fe1 te && well_formed_fp_exp fe2 te &&
                            (elen1 > 1) && (mlen1 > 1) && (elen1 <= mlen1) &&
                            (elen1 == elen2) && (mlen1 == mlen2)
    end
    with
    well_formed_fp_bexp (fb : fp_bexp) (te : SSATE.env) : bool :=
      match fb with
      | FBfalse
      | FBtrue => true
      | FBvar v => (exp_size v te) == 1
      | FBbveq fe1 fe2 => let (elen1, mlen1) := fp_exp_format fe1 in
                            let (elen2, mlen2) := fp_exp_format fe2 in
                              well_formed_fp_exp fe1 te && well_formed_fp_exp fe2 te &&
                              (elen1 > 1) && (mlen1 > 1) && (elen1 <= mlen1) &&
                              (elen1 == elen2) && (mlen1 == mlen2)
      | FBunop op fe => well_formed_fp_exp fe te
      | FBbinop op fe1 fe2 => let (elen1, mlen1) := fp_exp_format fe1 in
                              let (elen2, mlen2) := fp_exp_format fe2 in
                                well_formed_fp_exp fe1 te && well_formed_fp_exp fe2 te &&
                                (elen1 > 1) && (mlen1 > 1) && (elen1 <= mlen1) &&
                                (elen1 == elen2) && (mlen1 == mlen2)
      | FBlneg fb => well_formed_fp_bexp fb te
      | FBconj fb1 fb2
      | FBdisj fb1 fb2 => well_formed_fp_bexp fb1 te && well_formed_fp_bexp fb2 te
      end.

    Fixpoint well_formed_fp_bexps (bs : seq fp_bexp) (te : SSATE.env) : bool :=
      match bs with
      | [::] => true
      | b :: bs' => well_formed_fp_bexp b te && well_formed_fp_bexps bs' te
      end.

    Definition well_formed_unpackedbf (ubf : unpackedbf) (te : SSATE.env) : bool :=
      QFBV.well_formed_bexp (inf_flag ubf) te &&
      QFBV.well_formed_bexp (zero_flag ubf) te &&
      QFBV.well_formed_bexp (nan_flag ubf) te &&
      QFBV.well_formed_bexp (un_s ubf) te &&
      QFBV.well_formed_exp (un_e ubf) te &&
      QFBV.well_formed_exp (un_m ubf) te.
      
    Definition conform_unpackedbf (ubf : unpackedbf) (s : SSAStore.t) (te : SSATE.env) : bool :=
      conform_bexp (inf_flag ubf) s te &&
      conform_bexp (zero_flag ubf) s te &&
      conform_bexp (nan_flag ubf) s te &&
      conform_bexp (un_s ubf) s te &&
      conform_exp (un_e ubf) s te &&
      conform_exp (un_m ubf) s te.

End MakeFq2bvq.

Module Fq2bvq := MakeFq2bvq.