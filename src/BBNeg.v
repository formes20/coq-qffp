From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
From BitBlasting Require Import QFBV CNF BBCommon BBNot BBConst BBAdd.
From ssrlib Require Import ZAriths Tactics.
From nbits Require Import NBits.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* ===== bit_blast_neg ===== *)

Definition bit_blast_neg g ls : generator * cnf * word :=
  let '(g_not, cs_not, lrs_not) := bit_blast_not g ls in
  let '(g_con, cs_con, lrs_con) := bit_blast_const g_not (from_nat (size ls) 1) in
  let '(g_add, cs_add, lrs_add) := bit_blast_add g_con lrs_not lrs_con in
  (g_add, catrev cs_not (catrev cs_con cs_add), lrs_add).

Definition mk_env_neg E g ls : env * generator * cnf * word :=
  let '(E_not, g_not, cs_not, lrs_not) := mk_env_not E g ls in
  let '(E_con, g_con, cs_con, lrs_con) := mk_env_const E_not g_not (from_nat (size ls) 1) in
  let '(E_add, g_add, cs_add, lrs_add) := mk_env_add E_con g_con lrs_not lrs_con in
  (E_add, g_add, catrev cs_not (catrev cs_con cs_add), lrs_add).

Lemma bit_blast_neg_size_ss ls g g' (cs: cnf) (lrs: seq literal) :
  bit_blast_neg g ls = (g', cs, lrs) ->
  size ls = size lrs.
Proof.
  rewrite /bit_blast_neg. dcase (bit_blast_not g ls) => [[[g_not cs_not] lrs_not] Hbb_not].
  dcase (BBConst.bit_blast_const g_not (size ls) -bits of (1)%bits) =>
  [[[g_con cs_con] lrs_con] Hbb_con].
  dcase (bit_blast_add g_con lrs_not lrs_con) => [[[g_add cs_add] lrs_add] Hbb_add].
  case=> ? ? ?; subst. case: Hbb_con => ? ? ?; subst.
  move: (bit_blast_not_size_ss Hbb_not) => H. rewrite H.
  apply: (bit_blast_add_size_ss Hbb_add). rewrite size_map. rewrite size_from_nat.
  symmetry. assumption.
Qed.

Lemma bit_blast_neg_correct :
  forall g bs E ls g' cs lrs,
    bit_blast_neg g ls = (g', cs, lrs) ->
    enc_bits E ls bs ->
    interp_cnf E (add_prelude cs) ->
    enc_bits E lrs (negB bs).
Proof.
  move => g bs E ls g' cs lrs.
  rewrite /bit_blast_neg (lock bit_blast_const) (lock interp_cnf)/= -!lock.
  case Hnot : (bit_blast_not g ls) => [[g_not cs_not] lrs_not].
  case Hcons : (bit_blast_const g_not (from_nat (size ls) 1)) => [[g_con cs_con] lrs_con].
  case Hadd : (bit_blast_add g_con lrs_not lrs_con) => [[g_add cs_add] lrs_add].
  move => [] _ <- <-.
  rewrite !add_prelude_catrev.
  move => Hencbs Hcnf.
  move/andP : Hcnf => [Hcnfnot /andP [Hcnfcon Hcnfadd]].
  move : (bit_blast_not_correct  Hnot Hencbs Hcnfnot) => Henclrs_not.
  move : (bit_blast_const_correct Hcons Hcnfcon) => Henclrs_con.
  move : (addB1 (invB bs))=> Hencbr. rewrite /negB.
  move : (enc_bits_size Hencbs) => Hszeqls.
  move : (enc_bits_size Henclrs_not) => Hszeqlrsnot.
  move : (enc_bits_size Henclrs_con) => Hszeqlrscon. rewrite size_from_nat in Hszeqlrscon.
  rewrite -size_invB in Hszeqls. rewrite -Hszeqls in Hencbr. rewrite -Hszeqls -Hszeqlrscon in Hszeqlrsnot.
  exact : (bit_blast_add_correct Hadd Henclrs_not Henclrs_con Hencbr Hcnfadd Hszeqlrsnot).
Qed.

Lemma mk_env_neg_is_bit_blast_neg :
  forall E g ls E' g' cs lrs,
    mk_env_neg E g ls = (E', g', cs, lrs) ->
    bit_blast_neg g ls = (g', cs, lrs).
Proof.
  move => E g ls E' g' cs lrs.
  rewrite /mk_env_neg /bit_blast_neg.
  case Hmknot : (mk_env_not E g ls) => [[[E_not g_not] cs_not] lrs_not].
  rewrite (mk_env_not_is_bit_blast_not Hmknot).
  case Hmkcon : (mk_env_const E_not g_not (from_nat (size ls) 1)) => [[[E_con g_con] cs_con] lrs_con].
  rewrite (mk_env_const_is_bit_blast_const Hmkcon).
  case Hmkadd : (mk_env_add E_con g_con lrs_not lrs_con) => [[[E_add g_add] cs_add] lrs_add].
  rewrite (mk_env_add_is_bit_blast_add Hmkadd).
  by move => [] _ <- <- <-.
Qed.


Lemma mk_env_neg_sat :
  forall E g ls E' g' cs lrs,
    mk_env_neg E g ls = (E', g', cs, lrs) ->
    newer_than_lit g lit_ff ->
    newer_than_lits g ls ->
    interp_cnf E' cs.
Proof.
  rewrite /mk_env_neg => E g ls E' g' cs lrs.
  case Hmknot : (mk_env_not E g ls) => [[[E_not g_not] cs_not] lrs_not].
  case Hmkcon : (mk_env_const E_not g_not (from_nat (size ls) 1)) => [[[E_con g_con] cs_con] lrs_con].
  case Hmkadd : (mk_env_add E_con g_con lrs_not lrs_con) => [[[E_add g_add] cs_add] lrs_add].
  move => [] <-  _ <- _ Hnewtt Hnewls.
  rewrite !interp_cnf_catrev.
  move : (mk_env_not_sat Hmknot Hnewls) .
  move : (mk_env_const_sat Hmkcon) => Hcnfcon.
  move : (mk_env_not_newer_gen Hmknot)=> Hggnot.
  move : (mk_env_const_newer_gen Hmkcon) => Hgnotgcon.
  move : (mk_env_not_newer_res Hmknot Hnewls) => Hnotres.
  move : (mk_env_const_newer_res Hmkcon (newer_than_lit_le_newer Hnewtt Hggnot)) => Hconres.
  move : (bit_blast_not_size_ss (mk_env_not_is_bit_blast_not Hmknot)) => Hbbnotss.
  move : (mk_env_add_sat Hmkadd  (newer_than_lits_le_newer Hnotres Hgnotgcon) Hconres (newer_than_lit_le_newer Hnewtt (pos_leb_trans Hggnot Hgnotgcon))) => Hcnfadd.
  move : (mk_env_not_newer_cnf Hmknot Hnewls).
  rewrite /mk_env_const in Hmkcon.
  move : (mk_env_not_preserve Hmknot).
  move : Hmkcon => [] -> -> <- _.
  move => HEEcon Hnewcnfnot Hcnfnot.
  move : (mk_env_add_newer_gen Hmkadd) => Hgcongadd.
  move : (mk_env_add_preserve Hmkadd) => HEconEadd.
  rewrite (env_preserve_cnf HEconEadd Hnewcnfnot).
  by rewrite /= Hcnfnot Hcnfadd.
Qed.

Lemma mk_env_neg_preserve :
  forall E g ls E' g' cs lrs,
    mk_env_neg E g ls = (E', g', cs, lrs) ->
    env_preserve E E' g.
Proof.
  move => E g ls E' g' cs lrs.
  rewrite /mk_env_neg.
  case Hmknot : (mk_env_not E g ls) => [[[E_not g_not] cs_not] lrs_not].
  case Hmkcon : (mk_env_const E_not g_not (from_nat (size ls) 1)) => [[[E_con g_con] cs_con] lrs_con].
  case Hmkadd : (mk_env_add E_con g_con lrs_not lrs_con) => [[[E_add g_add] cs_add] lrs_add].
  move => [] <- _ _ _.
  move : (mk_env_not_preserve Hmknot) => HEEnot.
  move : (mk_env_const_preserve Hmkcon) => HEnotEcon.
  move : (mk_env_not_newer_gen Hmknot) => Hggnot.
  move : (mk_env_const_newer_gen Hmkcon) => Hgnotgcon.
  move : (mk_env_add_newer_gen Hmkadd) => Hgcongadd.
  move : (mk_env_add_preserve Hmkadd) => HEconEadd.
  move : (env_preserve_le HEnotEcon Hggnot) => HEnotEcong.
  move : (env_preserve_le HEconEadd (pos_leb_trans Hggnot Hgnotgcon)) => HEconEaddg.
  exact : (env_preserve_trans HEEnot (env_preserve_trans HEnotEcong HEconEaddg)).
Qed.

Lemma mk_env_neg_newer_gen :
  forall E g ls E' g' cs lrs,
    mk_env_neg E g ls = (E', g', cs, lrs) ->
    (g <=? g')%positive.
Proof.
  move => E g ls E' g' cs lrs.
  rewrite /mk_env_neg.
  case Hmknot : (mk_env_not E g ls) => [[[E_not g_not] cs_not] lrs_not].
  case Hmkcon : (mk_env_const E_not g_not (from_nat (size ls) 1)) => [[[E_con g_con] cs_con] lrs_con].
  case Hmkadd : (mk_env_add E_con g_con lrs_not lrs_con) => [[[E_add g_add] cs_add] lrs_add].
  move => [] _ <- _ _.
  move : (mk_env_not_newer_gen Hmknot) => Hggnot.
  move : (mk_env_const_newer_gen Hmkcon) => Hgnotgcon.
  move : (mk_env_add_newer_gen Hmkadd) => Hgcongadd.
  exact : (pos_leb_trans Hggnot (pos_leb_trans Hgnotgcon Hgcongadd)).
Qed.

Lemma mk_env_neg_newer_res :
  forall E g ls E' g' cs lrs,
    mk_env_neg E g ls = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls ->
    newer_than_lits g' lrs.
Proof.
  move => E g ls E' g' cs lrs.
  rewrite /mk_env_neg.
  case Hmknot : (mk_env_not E g ls) => [[[E_not g_not] cs_not] lrs_not].
  case Hmkcon : (mk_env_const E_not g_not (from_nat (size ls) 1)) => [[[E_con g_con] cs_con] lrs_con].
  case Hmkadd : (mk_env_add E_con g_con lrs_not lrs_con) => [[[E_add g_add] cs_add] lrs_add].
  move => [] _ <- _ <- Htt Hgls.
  exact : (mk_env_add_newer_res Hmkadd) => Hgaddlrsadd.
Qed.

Lemma mk_env_neg_newer_cnf :
  forall E g ls E' g' cs lrs,
    mk_env_neg E g ls = (E', g', cs, lrs) ->
    newer_than_lit g lit_tt ->
    newer_than_lits g ls ->
    newer_than_cnf g' cs.
Proof.
  move => E g ls E' g' cs lrs.
  rewrite /mk_env_neg.
  case Hmknot : (mk_env_not E g ls) => [[[E_not g_not] cs_not] lrs_not].
  case Hmkcon : (mk_env_const E_not g_not (from_nat (size ls) 1)) => [[[E_con g_con] cs_con] lrs_con].
  case Hmkadd : (mk_env_add E_con g_con lrs_not lrs_con) => [[[E_add g_add] cs_add] lrs_add].
  move => [] _ <- <- _ Htt Hgls.
  rewrite !newer_than_cnf_catrev.
  move : (mk_env_not_newer_gen Hmknot) => Hggnot.
  move : (mk_env_const_newer_gen Hmkcon) => Hgnotgcon.
  move : (mk_env_add_newer_gen Hmkadd) => Hgcongadd.
  move : (mk_env_not_newer_res Hmknot Hgls) => Hgnotresnot.
  move : (mk_env_const_newer_res Hmkcon (newer_than_lit_le_newer Htt Hggnot)) => Hgconlrscon.
  move : (bit_blast_not_size_ss (mk_env_not_is_bit_blast_not Hmknot)) => Hnotss.
  rewrite (mk_env_add_newer_cnf Hmkadd (newer_than_lits_le_newer Hgnotresnot Hgnotgcon) Hgconlrscon (newer_than_lit_le_newer Htt (pos_leb_trans Hggnot Hgnotgcon)) ) /=.
  move : (mk_env_not_newer_cnf Hmknot Hgls) => Hcnfnot.
  rewrite (newer_than_cnf_le_newer Hcnfnot (pos_leb_trans Hgnotgcon Hgcongadd)) /=.
  rewrite /mk_env_const in Hmkcon.
  by case :Hmkcon => _ _ <- _ /=.
Qed.

Lemma mk_env_neg_env_equal E1 E2 g ls E1' E2' g1' g2' cs1 cs2 lrs1 lrs2 :
  env_equal E1 E2 ->
  mk_env_neg E1 g ls = (E1', g1', cs1, lrs1) ->
  mk_env_neg E2 g ls = (E2', g2', cs2, lrs2) ->
  env_equal E1' E2' /\ g1' = g2' /\ cs1 = cs2 /\ lrs1 = lrs2.
Proof.
  rewrite /mk_env_neg => Heq.
  dcase (mk_env_not E1 g ls) => [[[[E_not1 g_not1] cs_not1] lrs_not1] Hnot1].
  dcase (mk_env_not E2 g ls) => [[[[E_not2 g_not2] cs_not2] lrs_not2] Hnot2].
  move: (mk_env_not_env_equal Heq Hnot1 Hnot2) => [Heq1 [? [? ?]]]; subst.
  rewrite /mk_env_const => /=.
  set ls' := [seq lit_of_bool i | i <- (size ls) -bits of (1)%bits].
  dcase (mk_env_add E_not1 g_not2 lrs_not2 ls')
  => [[[[E_add1 g_add1] cs_add1] lrs_add1] Hadd1].
  dcase (mk_env_add E_not2 g_not2 lrs_not2 ls')
  => [[[[E_add2 g_add2] cs_add2] lrs_add2] Hadd2].
  move: (mk_env_add_env_equal Heq1 Hadd1 Hadd2) => [Heq2 [? [? ?]]]; subst.
  case=> ? ? ? ?; case=> ? ? ? ?; subst. done.
Qed.
