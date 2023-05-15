From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From BitBlasting Require Import Typ TypEnv State AdhereConform.
From BitBlasting Require Import QFBV.

From ssrlib Require Import EqVar.
From WordBlasting Require Import fq2bvq WBExport.

Import QFBV.
Import QFBVNotation.
Import Fq2bvq.

Section WBMain.

  Definition feunop_denote (o : feunop) :=
   match o with
   | FUabs => abs_unpackedbf
   | FUneg => neg_unpackedbf
   end.
   
  Definition fermunop_denote (o : fermunop) :=
   match o with
   | FRUsqrt => sqrt_unpackbf
   | FRUrti => roundToIntegral_unpackbf
   end.
  
  Definition febinop_denote (o : febinop) :=
    match o with
    | FBmax => max_unpackedbf
    | FBmin => min_unpackedbf
    | FBrem => remrne_unpackbf
    end.
  
  Definition fermbinop_denote (o : fermbinop) :=
    match o with
    | FRBadd => add_unpackbf
    | FRBsub => sub_unpackbf
    | FRBmul => mul_unpackbf
    | FRBdiv => div_unpackbf
    end.
    
  Definition fermtriop_denote (o : fermtriop) :=
    match o with
    | FRTfma => fma_unpackbf
    end.
    
  Definition fbunop_denote (o : fbunop) :=
    match o with
    | FUisInfinite => isInfinite_unpackedbf
    | FUisZero => isZero_unpackedbf 
    | FUisNaN => isNaN_unpackedbf
    | FUisNegative => isNegative_unpackedbf 
    | FUisPositive => isPositive_unpackedbf
    | FUisNormal => isNormal_unpackedbf
    | FUisSubnormal => isSubNormal_unpackedbf
    end.

  Definition fbbinop_denote (o : fbbinop) :=
    match o with
    | FBeq => eq_unpackedbf
    | FBlt => lt_unpackedbf
    | FBgt => gt_unpackedbf
    | FBleq => le_unpackedbf
    | FBgeq => ge_unpackedbf
    end.
    
  Fixpoint word_blast_exp (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (fe : fp_exp) : SSATE.env * nat * seq bexp * unpackedbf * nat * nat :=
    match fe with
    | FEieee754 elen mlen s e m => ((unpack mlen elen gen_var g es te s e m), elen, mlen)
    | FEunop op fe => let '(te, g, es, ubf, elen, mlen) := (word_blast_exp gen_var g es te fe) in
                        ((feunop_denote op) mlen elen gen_var g es te ubf, elen, mlen)
    | FErmunop op rm fe => let '(te, g, es, ubf, elen, mlen) := (word_blast_exp gen_var g es te fe) in
                          ((fermunop_denote op) mlen elen gen_var g es te rm ubf, elen, mlen)
    | FEbinop op fe1 fe2 => let '(te, g, es, ubf1, elen, mlen) := (word_blast_exp gen_var g es te fe1) in
                            let '(te, g, es, ubf2, _, _) := (word_blast_exp gen_var g es te fe2) in
                              ((febinop_denote op) mlen elen gen_var g es te ubf1 ubf2, elen, mlen)
    | FErmbinop op rm fe1 fe2 => let '(te, g, es, ubf1, elen, mlen) := (word_blast_exp gen_var g es te fe1) in
                                 let '(te, g, es, ubf2, _, _) := (word_blast_exp gen_var g es te fe2) in
                                   ((fermbinop_denote op) mlen elen gen_var g es te rm ubf1 ubf2, elen, mlen)
    | FErmtriop op rm fe1 fe2 fe3 => let '(te, g, es, ubf1, elen, mlen) := (word_blast_exp gen_var g es te fe1) in
                                     let '(te, g, es, ubf2, _, _) := (word_blast_exp gen_var g es te fe2) in
                                     let '(te, g, es, ubf3, _, _) := (word_blast_exp gen_var g es te fe3) in
                                      ((fermtriop_denote op) mlen elen gen_var g es te rm ubf1 ubf2 ubf3, elen, mlen)
    | FEofbf rm fe telen tmlen => let '(te, g, es, ubf, elen, mlen) := (word_blast_exp gen_var g es te fe) in
                                   ((of_unpackbf gen_var g es te rm ubf elen mlen telen tmlen), telen, tmlen)
    | FEofbv e n telen tmlen => ((unpack tmlen telen gen_var g es te (s_exp tmlen telen e) (e_exp tmlen telen e) (m_exp tmlen e)), telen, tmlen)
    | FEofsbv rm e n telen tmlen => ((of_sbv_unpackbf gen_var g es te rm e n telen tmlen), telen, tmlen)
    | FEofubv rm e n telen tmlen => ((of_ubv_unpackbf gen_var g es te rm e n telen tmlen), telen, tmlen)
    | FEite fb fe1 fe2 => let '(te, g, es, be) := (word_blast_bexp gen_var g es te fb) in
                          let '(te, g, es, ubf1, elen, mlen) := (word_blast_exp gen_var g es te fe1) in
                          let '(te, g, es, ubf2, _, _) := (word_blast_exp gen_var g es te fe2) in
                          let inf_flag := Eite_bexp be (inf_flag ubf1) (inf_flag ubf2) in
                          let zero_flag := Eite_bexp be (zero_flag ubf1) (zero_flag ubf2) in
                          let nan_flag := Eite_bexp be (nan_flag ubf1) (nan_flag ubf2) in
                          let un_s := Eite_bexp be (un_s ubf1) (un_s ubf2) in
                          let un_e := Eite be (un_e ubf1) (un_e ubf2) in
                          let un_m := Eite be (un_m ubf1) (un_m ubf2) in
                          let result := Build_unpackedbf inf_flag zero_flag nan_flag un_s un_e un_m in
                            (te, g, es, result, elen, mlen)
    end
    with
    word_blast_bexp (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (fb : fp_bexp) : SSATE.env * nat * seq bexp * bexp :=
      match fb with
      | FBfalse => (te, g, es, Bfalse)
      | FBtrue => (te, g, es, Btrue)
      | FBvar v => (te, g, es, Bbinop Beq v (Econst [::true]))
      | FBbveq fe1 fe2 => let '(te, g, es, ubf1, elen, mlen) := (word_blast_exp gen_var g es te fe1) in
                          let '(te, g, es, ubf2, _, _) := (word_blast_exp gen_var g es te fe2) in
                          let '(s1, e1, m1) := pack mlen elen ubf1 in
                          let '(s2, e2, m2) := pack mlen elen ubf2 in
                            (te, g, es, ((Bbinop Beq s1 s2) /\# (Bbinop Beq e1 e2) /\# (Bbinop Beq m1 m2)))
      | FBunop op fe => let '(te, g, es, ubf, elen, mlen) := (word_blast_exp gen_var g es te fe) in
                          (te, g, es, ((fbunop_denote op) mlen elen ubf))
      | FBbinop op fe1 fe2 => let '(te, g, es, ubf1, elen, mlen) := (word_blast_exp gen_var g es te fe1) in
                              let '(te, g, es, ubf2, _, _) := (word_blast_exp gen_var g es te fe2) in
                                (te, g, es, ((fbbinop_denote op) mlen elen ubf1 ubf2))
      | FBlneg fb => let '(te, g, es, fb') := word_blast_bexp gen_var g es te fb in
                       (te, g, es, (Blneg fb'))
      | FBconj fb1 fb2 => let '(te, g, es, fb1') := word_blast_bexp gen_var g es te fb1 in
                          let '(te, g, es, fb2') := word_blast_bexp gen_var g es te fb2 in
                            (te, g, es, (Bconj fb1' fb2'))
      | FBdisj fb1 fb2 => let '(te, g, es, fb1') := word_blast_bexp gen_var g es te fb1 in
                          let '(te, g, es, fb2') := word_blast_bexp gen_var g es te fb2 in
                            (te, g, es, (Bdisj fb1' fb2'))
      end. 

  Fixpoint word_blast_bexps (gen_var : nat -> (ssavar * nat)) (g : nat) (es : seq bexp) (te : SSATE.env) (fes : seq fp_bexp) : SSATE.env * nat * seq bexp :=
     match fes with
    | [::] => (te, g, es)
    | fb :: fbs' => let '(te', g', es', b) := word_blast_bexp gen_var g es te fb in
                      word_blast_bexps gen_var g' (b::es') te' fbs'
    end.
    
End WBMain.
