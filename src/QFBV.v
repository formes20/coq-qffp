
From Coq Require Import Arith ZArith OrderedType String.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From ssrlib Require Import EqVar Types EqOrder Nats ZAriths EqStore EqFSets Tactics Seqs Strings.
From BitBlasting Require Import Typ TypEnv State.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Module MakeQFBV
       (V : EqOrder)
       (VP : Printer with Definition t := V.t)
       (VS : EqFSet with Module SE := V)
       (TE : TypEnv with Module SE := V)
       (S : BitsStore V TE).

  Module VSLemmas := FSetLemmas VS.

  Local Notation var := V.t.

  (* Syntax of expressions and Boolean expressions *)

  Inductive eunop : Set :=
  | Unot
  | Uneg
  | Uextr : nat -> nat -> eunop
(*| Uslice : nat -> nat -> nat -> eunop *)
  | Uhigh : nat -> eunop
  | Ulow : nat -> eunop
  | Uzext : nat -> eunop
  | Usext : nat -> eunop
  | Urepeat : nat -> eunop
  | Urotl : nat -> eunop
  | Urotr : nat -> eunop.

  Inductive ebinop : Set :=
  | Band
  | Bor
  | Bxor
  | Badd
  | Bsub
  | Bmul
  (*div*)
  | Bdiv
  | Bmod
  | Bsdiv
  | Bsrem
  | Bsmod
  | Bshl
  | Blshr
  | Bashr
  | Bconcat (* Bconcat high_bits low_bits *)
  | Bcomp.

  Inductive bbinop : Set :=
  | Beq
  | Bult
  | Bule
  | Bugt
  | Buge
  | Bslt
  | Bsle
  | Bsgt
  | Bsge
  | Buaddo
  | Busubo
  | Bumulo
  | Bsaddo
  | Bssubo
  | Bsmulo.

  (* The fewer constructors the better *)
  Inductive exp : Type :=
  | Evar : var -> exp
  | Econst : bits -> exp
  | Eunop : eunop -> exp -> exp
  | Ebinop : ebinop -> exp -> exp -> exp
  | Eite : bexp -> exp -> exp -> exp
  with
  bexp : Type :=
  | Bfalse : bexp
  | Btrue : bexp
  | Bbinop : bbinop -> exp -> exp -> bexp
  | Blneg : bexp -> bexp
  | Bconj : bexp -> bexp -> bexp
  | Bdisj : bexp -> bexp -> bexp.

  (* Equality of unary operators in expressions *)

  Definition eunop_eqn (o1 o2 : eunop) : bool :=
    match o1, o2 with
    | Unot, Unot
    | Uneg, Uneg => true
    | Uextr i1 j1, Uextr i2 j2 => (i1 == i2) && (j1 == j2)
(*  | Uslice v1 v2 v3, Uslice w1 w2 w3 => (v1 == w1) && (v2 == w2) && (v3 == w3) *)
    | Uhigh n1, Uhigh n2
    | Ulow n1, Ulow n2
    | Uzext n1, Uzext n2
    | Usext n1, Usext n2
    | Urepeat n1, Urepeat n2
    | Urotl n1, Urotl n2
    | Urotr n1, Urotr n2 => n1 == n2
    | _, _ => false
    end.

  Lemma eunop_eqn_refl o : eunop_eqn o o.
  Proof. case: o => //=; move=> *; rewrite !eqxx; done. Qed.

  Lemma eunop_eqn_eq o1 o2 : eunop_eqn o1 o2 <-> o1 = o2.
  Proof.
    split; case: o1; case: o2 => //=.
    - move=> n1 n2 n3 n4. move/andP => [/eqP -> /eqP ->]. reflexivity.
    (* - move=> n1 n2 n3 n4 n5 n6. move/andP => [/andP [/eqP -> /eqP ->] /eqP ->] //. *)
    - move=> n1 n2. move/eqP=> -> //.
    - move=> n1 n2. move/eqP=> -> //.
    - move=> n1 n2. move/eqP=> -> //.
    - move=> n1 n2. move/eqP=> -> //.
    - move=> n1 n2. move/eqP=> -> //.
    - move=> n1 n2. move/eqP=> -> //.
    - move=> n1 n2. move/eqP=> -> //.
    - move=> n1 n2 n3 n4. case=> -> ->. by rewrite !eqxx.
    (* - move=> n1 n2 n3 n4 n5 n6. case=> -> -> ->. by rewrite !eqxx. *)
    - move=> n1 n2. case=> ->. by rewrite !eqxx.
    - move=> n1 n2. case=> ->. by rewrite !eqxx.
    - move=> n1 n2. case=> ->. by rewrite !eqxx.
    - move=> n1 n2. case=> ->. by rewrite !eqxx.
    - move=> n1 n2. case=> ->. by rewrite !eqxx.
    - move=> n1 n2. case=> ->. by rewrite !eqxx.
    - move=> n1 n2. case=> ->. by rewrite !eqxx.
  Qed.

  Lemma eunop_eqP (o1 o2 : eunop) : reflect (o1 = o2) (eunop_eqn o1 o2).
  Proof.
    case H: (eunop_eqn o1 o2).
    - apply: ReflectT. apply/eunop_eqn_eq. assumption.
    - apply: ReflectF. move=> Heq. move/negP: H. apply. apply/eunop_eqn_eq.
      assumption.
  Qed.

  Definition eunop_eqMixin := EqMixin eunop_eqP.
  Canonical eunop_eqType := Eval hnf in EqType eunop eunop_eqMixin.

  (* Equality of binary operators in expressions *)

  Definition ebinop_eqn (o1 o2 : ebinop) : bool :=
    match o1, o2 with
    | Band, Band
    | Bor, Bor
    | Bxor, Bxor
    | Badd, Badd
    | Bsub, Bsub
    | Bmul, Bmul
    | Bdiv, Bdiv
    | Bmod, Bmod
    | Bsdiv, Bsdiv
    | Bsrem, Bsrem
    | Bsmod, Bsmod
    | Bshl, Bshl
    | Blshr, Blshr
    | Bashr, Bashr
    | Bconcat, Bconcat
    | Bcomp, Bcomp => true
    | _, _ => false
    end.

  Lemma ebinop_eqn_refl o : ebinop_eqn o o.
  Proof. case: o => //=; move=> *; rewrite !eqxx; done. Qed.

  Lemma ebinop_eqn_eq o1 o2 : ebinop_eqn o1 o2 <-> o1 = o2.
  Proof. by split; case: o1; case: o2 => //=. Qed.

  Lemma ebinop_eqP (o1 o2 : ebinop) : reflect (o1 = o2) (ebinop_eqn o1 o2).
  Proof.
    case H: (ebinop_eqn o1 o2).
    - apply: ReflectT. apply/ebinop_eqn_eq. assumption.
    - apply: ReflectF. move=> Heq. move/negP: H. apply. apply/ebinop_eqn_eq.
      assumption.
  Qed.

  Definition ebinop_eqMixin := EqMixin ebinop_eqP.
  Canonical ebinop_eqType := Eval hnf in EqType ebinop ebinop_eqMixin.

  (* Equality of binary operators in Boolean expressions *)

  Definition bbinop_eqn (o1 o2 : bbinop) : bool :=
    match o1, o2 with
    | Beq, Beq
    | Bult, Bult
    | Bule, Bule
    | Bugt, Bugt
    | Buge, Buge
    | Bslt, Bslt
    | Bsle, Bsle
    | Bsgt, Bsgt
    | Bsge, Bsge
    | Buaddo, Buaddo
    | Busubo, Busubo
    | Bumulo, Bumulo
    | Bsaddo, Bsaddo
    | Bssubo, Bssubo
    | Bsmulo, Bsmulo => true
    | _, _ => false
    end.

  Lemma bbinop_eqn_refl o : bbinop_eqn o o.
  Proof. case: o => //=; move=> *; rewrite !eqxx; done. Qed.

  Lemma bbinop_eqn_eq o1 o2 : bbinop_eqn o1 o2 <-> o1 = o2.
  Proof. by split; case: o1; case: o2 => //=. Qed.

  Lemma bbinop_eqP (o1 o2 : bbinop) : reflect (o1 = o2) (bbinop_eqn o1 o2).
  Proof.
    case H: (bbinop_eqn o1 o2).
    - apply: ReflectT. apply/bbinop_eqn_eq. assumption.
    - apply: ReflectF. move=> Heq. move/negP: H. apply. apply/bbinop_eqn_eq.
      assumption.
  Qed.

  Definition bbinop_eqMixin := EqMixin bbinop_eqP.
  Canonical bbinop_eqType := Eval hnf in EqType bbinop bbinop_eqMixin.

  (* Equality of expressions and Boolean expressions *)

  Fixpoint exp_eqn (e1 e2 : exp) : bool :=
    match e1, e2 with
    | Evar v1, Evar v2 => v1 == v2
    | Econst n1, Econst n2 => n1 == n2
    | Eunop op1 e1, Eunop op2 e2 => (op1 == op2) && (exp_eqn e1 e2)
    | Ebinop op1 e1 e2, Ebinop op2 e3 e4 =>
      (op1 == op2) && (exp_eqn e1 e3) && (exp_eqn e2 e4)
    | Eite c1 e1 e2, Eite c2 e3 e4 =>
      (bexp_eqn c1 c2) && (exp_eqn e1 e3) && (exp_eqn e2 e4)
    | _, _ => false
    end
  with
  bexp_eqn (e1 e2 : bexp) : bool :=
    match e1, e2 with
    | Bfalse, Bfalse => true
    | Btrue, Btrue => true
    | Bbinop op1 e1 e2, Bbinop op2 e3 e4 =>
      (op1 == op2) && (exp_eqn e1 e3) && (exp_eqn e2 e4)
    | Blneg e1, Blneg e2 => bexp_eqn e1 e2
    | Bconj e1 e2, Bconj e3 e4 => (bexp_eqn e1 e3) && (bexp_eqn e2 e4)
    | Bdisj e1 e2, Bdisj e3 e4 => (bexp_eqn e1 e3) && (bexp_eqn e2 e4)
    | _, _ => false
    end.

  Lemma exp_eqn_eq (e1 e2 : exp) : exp_eqn e1 e2 -> e1 = e2
  with
  bexp_eqn_eq (e1 e2 : bexp) : bexp_eqn e1 e2 -> e1 = e2.
  Proof.
    (* exp_eqn_eq *)
    case: e1; case: e2 => /=; try discriminate.
    - move=> v1 v2 /eqP ->; reflexivity.
    - move=> b1 b2 Hb. rewrite (eqP Hb). reflexivity.
    - move=> op1 e1 op2 e2 /andP [/eqP -> H]. rewrite (exp_eqn_eq _ _ H). reflexivity.
    - move=> op1 e1 e2 op2 e3 e4 /andP [/andP [/eqP ->] H1 H2].
      rewrite (exp_eqn_eq _ _ H1) (exp_eqn_eq _ _ H2). reflexivity.
    - move=> c1 e1 e2 c2 e3 e4 /andP [/andP [H1 H2] H3].
      rewrite (bexp_eqn_eq _ _ H1) (exp_eqn_eq _ _ H2) (exp_eqn_eq _ _ H3); reflexivity.
    (* bexp_eqn_eq *)
    case: e1; case: e2 => /=; try discriminate.
    - reflexivity.
    - reflexivity.
    - move=> op1 e1 e2 op2 e3 e4 /andP [/andP [/eqP -> H1] H2].
      rewrite (exp_eqn_eq _ _ H1) (exp_eqn_eq _ _ H2); reflexivity.
    - move=> e1 e2 H. rewrite (bexp_eqn_eq _ _ H); reflexivity.
    - move=> e1 e2 e3 e4 /andP [H1 H2].
      rewrite (bexp_eqn_eq _ _ H1) (bexp_eqn_eq _ _ H2); reflexivity.
    - move=> e1 e2 e3 e4 /andP [H1 H2].
      rewrite (bexp_eqn_eq _ _ H1) (bexp_eqn_eq _ _ H2); reflexivity.
  Qed.

  Lemma exp_eqn_refl (e : exp) : exp_eqn e e
  with
  bexp_eqn_refl (e : bexp) : bexp_eqn e e.
  Proof.
    (* exp_eqn_refl *)
    case: e => /=.
    - move=> v; exact: eqxx.
    - move=> b; by exact: eqxx.
    - move=> op e; by rewrite eqxx exp_eqn_refl.
    - move=> op e1 e2; by rewrite eqxx (exp_eqn_refl e1) (exp_eqn_refl e2).
    - move=> c e1 e2; by rewrite (bexp_eqn_refl c) (exp_eqn_refl e1) (exp_eqn_refl e2).
    (* bexp_eqn_refl *)
    case: e => /=.
    - done.
    - done.
    - move=> op e1 e2; by rewrite eqxx (exp_eqn_refl e1) (exp_eqn_refl e2).
    - move=> e; exact: bexp_eqn_refl.
    - move=> e1 e2; by rewrite (bexp_eqn_refl e1) (bexp_eqn_refl e2).
    - move=> e1 e2; by rewrite (bexp_eqn_refl e1) (bexp_eqn_refl e2).
  Qed.

  Lemma exp_eqn_sym {e1 e2 : exp} : exp_eqn e1 e2 -> exp_eqn e2 e1.
  Proof. move=> H. rewrite (exp_eqn_eq H). exact: exp_eqn_refl. Qed.

  Lemma bexp_eqn_sym {e1 e2 : bexp} : bexp_eqn e1 e2 -> bexp_eqn e2 e1.
  Proof. move=> H. rewrite (bexp_eqn_eq H). exact: bexp_eqn_refl. Qed.

  Lemma exp_eqn_trans {e1 e2 e3 : exp} :
    exp_eqn e1 e2 -> exp_eqn e2 e3 -> exp_eqn e1 e3.
  Proof.
    move=> H1 H2. rewrite (exp_eqn_eq H1) (exp_eqn_eq H2). exact: exp_eqn_refl.
  Qed.

  Lemma bexp_eqn_trans {e1 e2 e3 : bexp} :
    bexp_eqn e1 e2 -> bexp_eqn e2 e3 -> bexp_eqn e1 e3.
  Proof.
    move=> H1 H2. rewrite (bexp_eqn_eq H1) (bexp_eqn_eq H2). exact: bexp_eqn_refl.
  Qed.

  Lemma exp_eqP (e1 e2 : exp) : reflect (e1 = e2) (exp_eqn e1 e2).
  Proof.
    case H: (exp_eqn e1 e2).
    - apply: ReflectT. exact: (exp_eqn_eq H).
    - apply: ReflectF => Heq. move/negP: H; apply. rewrite Heq. exact: exp_eqn_refl.
  Qed.

  Lemma bexp_eqP (e1 e2 : bexp) : reflect (e1 = e2) (bexp_eqn e1 e2).
  Proof.
    case H: (bexp_eqn e1 e2).
    - apply: ReflectT. exact: (bexp_eqn_eq H).
    - apply: ReflectF => Heq. move/negP: H; apply. rewrite Heq. exact: bexp_eqn_refl.
  Qed.

  Definition exp_eqMixin := EqMixin exp_eqP.
  Definition bexp_eqMixin := EqMixin bexp_eqP.
  Canonical exp_eqType := Eval hnf in EqType exp exp_eqMixin.
  Canonical bexp_eqType := Eval hnf in EqType bexp bexp_eqMixin.


  (** QF_BV constructors. *)

  Definition qfbv_true := Btrue.

  Definition qfbv_false := Bfalse.

  Definition qfbv_var v := Evar v.

  Definition qfbv_const w n := Econst (NBitsDef.from_nat w n).

  Definition qfbv_const_bits bs := Econst bs.

  Definition qfbv_const_nat w n := Econst (NBitsDef.from_nat w n).

  Definition qfbv_const_Z w n := Econst (NBitsDef.from_Z w n).

  Definition qfbv_const_N w n := Econst (NBitsDef.from_N w n).

  Definition qfbv_zero w := Econst (NBitsDef.from_nat w 0).

  Definition qfbv_one w := Econst (NBitsDef.from_nat w 1).

  Definition qfbv_not qe := Eunop Unot qe.

  Definition qfbv_neg qe := Eunop Uneg qe.

  Definition qfbv_extr i j qe := Eunop (Uextr i j) qe.

  Definition qfbv_high n qe := Eunop (Uhigh n) qe.

  Definition qfbv_low n qe := Eunop (Ulow n) qe.

  Definition qfbv_zext n qe := Eunop (Uzext n) qe.

  Definition qfbv_sext n qe := Eunop (Usext n) qe.

  Definition qfbv_and qe0 qe1 := Ebinop Band qe0 qe1.

  Definition qfbv_or qe0 qe1 := Ebinop Bor qe0 qe1.

  Definition qfbv_xor qe0 qe1 := Ebinop Bxor qe0 qe1.

  Definition qfbv_add qe0 qe1 := Ebinop Badd qe0 qe1.

  Definition qfbv_sub qe0 qe1 := Ebinop Bsub qe0 qe1.

  Definition qfbv_mul qe0 qe1 := Ebinop Bmul qe0 qe1.

  Definition qfbv_mod qe0 qe1 := Ebinop Bmod qe0 qe1.

  Definition qfbv_srem qe0 qe1 := Ebinop Bsrem qe0 qe1.

  Definition qfbv_smod qe0 qe1 := Ebinop Bsmod qe0 qe1.

  Definition qfbv_shl qe0 qe1 := Ebinop Bshl qe0 qe1.

  Definition qfbv_lshr qe0 qe1 := Ebinop Blshr qe0 qe1.

  Definition qfbv_ashr qe0 qe1 := Ebinop Bashr qe0 qe1.

  Definition qfbv_concat qe0 qe1 := Ebinop Bconcat qe0 qe1.

  Definition qfbv_eq qe0 qe1 := Bbinop Beq qe0 qe1.

  Definition qfbv_ult qe0 qe1 := Bbinop Bult qe0 qe1.

  Definition qfbv_ule qe0 qe1 := Bbinop Bule qe0 qe1.

  Definition qfbv_ugt qe0 qe1 := Bbinop Bugt qe0 qe1.

  Definition qfbv_uge qe0 qe1 := Bbinop Buge qe0 qe1.

  Definition qfbv_slt qe0 qe1 := Bbinop Bslt qe0 qe1.

  Definition qfbv_sle qe0 qe1 := Bbinop Bsle qe0 qe1.

  Definition qfbv_sgt qe0 qe1 := Bbinop Bsgt qe0 qe1.

  Definition qfbv_sge qe0 qe1 := Bbinop Bsge qe0 qe1.

  Definition qfbv_uaddo qe0 qe1 := Bbinop Buaddo qe0 qe1.

  Definition qfbv_usubo qe0 qe1 := Bbinop Busubo qe0 qe1.

  Definition qfbv_umulo qe0 qe1 := Bbinop Bumulo qe0 qe1.

  Definition qfbv_saddo qe0 qe1 := Bbinop Bsaddo qe0 qe1.

  Definition qfbv_ssubo qe0 qe1 := Bbinop Bssubo qe0 qe1.

  Definition qfbv_smulo qe0 qe1 := Bbinop Bsmulo qe0 qe1.

  Definition qfbv_lneg qb := Blneg qb.

  Definition qfbv_conj qb0 qb1 := Bconj qb0 qb1.

  Definition qfbv_disj qb0 qb1 := Bdisj qb0 qb1.

  Definition qfbv_ite qb qe0 qe1 := Eite qb qe0 qe1.

  Definition qfbv_imp f g := qfbv_disj (qfbv_lneg f) g.


  (* Semantics of expressions and Boolean expressions *)

  Local Notation state := S.t.

  Definition eunop_denote (o : eunop) : bits -> bits :=
    match o with
    | Unot => invB
    | Uneg => negB
    | Uextr i j => extract i j
(*  | Uslice w1 w2 w3 => *)
    | Uhigh n => high n
    | Ulow n => low n
    | Uzext n => zext n
    | Usext n => sext n
    | Urepeat n => repeat n
    | Urotl n => rolB n
    | Urotr n => rorB n
    end.

  Definition ebinop_denote (o : ebinop) : bits -> bits -> bits :=
    match o with
    | Band => andB
    | Bor => orB
    | Bxor => xorB
    | Badd => addB
    | Bsub => subB
    | Bmul => mulB
    | Bdiv => udivB'
    | Bmod => uremB
    | Bsdiv => sdivB
    | Bsrem => sremB
    | Bsmod => smodB
    | Bshl => fun b1 b2 => shlBB b1 b2
    | Blshr => fun b1 b2 => shrBB b1 b2
    | Bashr => fun b1 b2 => sarBB b1 b2
    | Bconcat => fun b1 b2 => cat b2 b1
    | Bcomp => fun b1 b2 => [:: eq_op b1 b2]
    end.

  Definition bbinop_denote (o : bbinop) : bits -> bits -> bool :=
    match o with
    | Beq => eq_op
    | Bult => ltB
    | Bule => leB
    | Bugt => gtB
    | Buge => geB
    | Bslt => sltB
    | Bsle => sleB
    | Bsgt => sgtB
    | Bsge => sgeB
    | Buaddo => carry_addB
    | Busubo => borrow_subB
    | Bumulo => Umulo
    | Bsaddo => Saddo
    | Bssubo => Ssubo
    | Bsmulo => Smulo
    end.

  Fixpoint eval_exp (e : exp) (s : state) : bits :=
    match e with
    | Evar v => S.acc v s
    | Econst n => n
    | Eunop op e => (eunop_denote op) (eval_exp e s)
    | Ebinop op e1 e2 => (ebinop_denote op) (eval_exp e1 s) (eval_exp e2 s)
    | Eite b e1 e2 => if eval_bexp b s then eval_exp e1 s else eval_exp e2 s
    end
    with
    eval_bexp (e : bexp) (s : state) : bool :=
      match e with
      | Bfalse => false
      | Btrue => true
      | Bbinop op e1 e2 => (bbinop_denote op) (eval_exp e1 s) (eval_exp e2 s)
      | Blneg e => ~~ (eval_bexp e s)
      | Bconj e1 e2 => (eval_bexp e1 s) && (eval_bexp e2 s)
      | Bdisj e1 e2 => (eval_bexp e1 s) || (eval_bexp e2 s)
      end.

  Definition valid E (e : bexp) : Prop :=
    forall s, S.conform s E -> eval_bexp e s.

  Notation valid_bexp := valid.

  Definition sat E (e : bexp) : Prop :=
    exists s, S.conform s E /\ eval_bexp e s.

  Lemma valid_unsat E e : valid E e -> ~ (sat E (Blneg e)).
  Proof.
    move=> H [s /= [Hco He]]. apply/idP: He. exact: (H _ Hco).
  Qed.


  (* Variables in expressions *)

  Fixpoint vars_exp (e : exp) : VS.t :=
    match e with
    | Evar v => VS.singleton v
    | Econst n => VS.empty
    | Eunop op e => vars_exp e
    | Ebinop op e1 e2 => VS.union (vars_exp e1) (vars_exp e2)
    | Eite b e1 e2 => VS.union (vars_bexp b) (VS.union (vars_exp e1) (vars_exp e2))
    end
  with
  vars_bexp (e : bexp) : VS.t :=
    match e with
    | Bfalse
    | Btrue => VS.empty
    | Bbinop op e1 e2 => VS.union (vars_exp e1) (vars_exp e2)
    | Blneg e => vars_bexp e
    | Bconj e1 e2
    | Bdisj e1 e2 => VS.union (vars_bexp e1) (vars_bexp e2)
    end.

  Fixpoint vars_bexps (es : seq bexp) : VS.t :=
    match es with
    | [::] => VS.empty
    | e::es => VS.union (vars_bexp e) (vars_bexps es)
    end.

  Lemma vars_bexps_cons e es : vars_bexps (e::es) = VS.union (vars_bexp e) (vars_bexps es).
  Proof. reflexivity. Qed.

  Lemma vars_bexps_rcons es e :
    VS.Equal (vars_bexps (rcons es e)) (VS.union (vars_bexps es) (vars_bexp e)).
  Proof.
    elim: es => [| hd tl IH] //=.
    - by VSLemmas.dp_Equal.
    - rewrite IH. by VSLemmas.dp_Equal.
  Qed.

  Lemma vars_bexps_cat es1 es2 :
    VS.Equal (vars_bexps (es1 ++ es2)) (VS.union (vars_bexps es1) (vars_bexps es2)).
  Proof.
    elim: es1 es2 => [| e1 es1 IH] es2 //=.
    - by VSLemmas.dp_Equal.
    - rewrite IH. by VSLemmas.dp_Equal.
  Qed.

  Lemma vars_bexps_rev es :
    VS.Equal (vars_bexps (rev es)) (vars_bexps es).
  Proof.
    elim: es => [| e es IH] //=. rewrite rev_cons vars_bexps_rcons.
    rewrite IH. rewrite VSLemmas.P.union_sym. reflexivity.
  Qed.


  (* Ordering on expressions *)

  Definition id_eunop (op : eunop) : nat :=
    match op with
    | Unot => 0
    | Uneg => 1
    | Uextr i j => 2
(*  | Uslice w1 w2 w3 => 3 *)
    | Uhigh n => 4
    | Ulow n => 5
    | Uzext n => 6
    | Usext n => 7
    | Urepeat n => 8
    | Urotl n => 9
    | Urotr n => 10
    end.

  Definition eunop_ltn (o1 o2 : eunop) : bool :=
    match o1, o2 with
    | Uextr i1 j1, Uextr i2 j2 => (i1 < i2) || ((i1 == i2) && (j1 < j2))
(*  | Uslice u1 u2 u3, Uslice w1 w2 w3 =>
      (u1 < w1) || ((u1 == w1) && (u2 < w2))
      || ((u1 == w1) && (u2 == w2) && (u3 < w3)) *)
    | Uhigh n1, Uhigh n2
    | Ulow n1, Ulow n2
    | Uzext n1, Uzext n2
    | Usext n1, Usext n2
    | Urepeat n1, Urepeat n2
    | Urotl n1, Urotl n2
    | Urotr n1, Urotr n2 => n1 < n2
    | _, _ => id_eunop o1 < id_eunop o2
    end.

  Lemma eunop_ltnn o : eunop_ltn o o = false.
  Proof. by case: o => //=; intros; rewrite ?eqxx ?ltnn. Qed.

  Lemma eunop_ltn_eqF o1 o2 : eunop_ltn o1 o2 -> o1 == o2 = false.
  Proof.
    move=> Hlt; apply/negP => Heq; rewrite (eqP Heq) eunop_ltnn in Hlt; discriminate.
  Qed.

  Ltac t_auto_hook ::=
    match goal with
    | H1 : is_true (?e1 < ?e2), H2 : is_true (?e2 < ?e3) |- context [?e1 < ?e3] =>
      rewrite (ltn_trans H1 H2); clear H1 H2
    end.

  Lemma eunop_ltn_trans o1 o2 o3 :
    eunop_ltn o1 o2 -> eunop_ltn o2 o3 -> eunop_ltn o1 o3.
  Proof. case: o1; case: o2; case: o3 => //=; by t_auto. Qed.

  Lemma eunop_eqn_ltn_gtn o1 o2 : (o1 == o2) || (eunop_ltn o1 o2) || (eunop_ltn o2 o1).
  Proof.
    case: o1; case: o2 => //=.
    - move=> n1 n2 n3 n4. move: (eqn_ltn_gtn_cases n1 n3) (eqn_ltn_gtn_cases n2 n4).
      by t_auto.
 (* - move=> n1 n2 n3 n4 n5 n6.
      move: (eqn_ltn_gtn_cases n1 n4) (eqn_ltn_gtn_cases n2 n5)
                                      (eqn_ltn_gtn_cases n3 n6).
      by t_auto. *)
    - move=> n1 n2. move: (eqn_ltn_gtn_cases n1 n2); by t_auto.
    - move=> n1 n2. move: (eqn_ltn_gtn_cases n1 n2); by t_auto.
    - move=> n1 n2. move: (eqn_ltn_gtn_cases n1 n2); by t_auto.
    - move=> n1 n2. move: (eqn_ltn_gtn_cases n1 n2); by t_auto.
    - move=> n1 n2. move: (eqn_ltn_gtn_cases n1 n2); by t_auto.
    - move=> n1 n2. move: (eqn_ltn_gtn_cases n1 n2); by t_auto.
    - move=> n1 n2. move: (eqn_ltn_gtn_cases n1 n2); by t_auto.
  Qed.

  Definition id_ebinop (o : ebinop) : nat :=
    match o with
    | Band => 0
    | Bor => 1
    | Bxor => 2
    | Badd => 3
    | Bsub => 4
    | Bmul => 5
    | Bdiv => 6
    | Bmod => 7
    | Bsdiv => 8
    | Bsrem => 9
    | Bsmod => 10
    | Bshl => 11
    | Blshr => 12
    | Bashr => 13
    | Bconcat => 14
    | Bcomp => 15
    end.

  Definition ebinop_ltn (o1 o2 : ebinop) : bool := id_ebinop o1 < id_ebinop o2.

  Lemma ebinop_ltnn o : ebinop_ltn o o = false.
  Proof. exact: ltnn. Qed.

  Lemma ebinop_ltn_eqF o1 o2 : ebinop_ltn o1 o2 -> o1 == o2 = false.
  Proof.
    move=> Hlt; apply/negP => Heq; rewrite (eqP Heq) ebinop_ltnn in Hlt; discriminate.
  Qed.

  Lemma ebinop_ltn_trans o1 o2 o3 :
    ebinop_ltn o1 o2 -> ebinop_ltn o2 o3 -> ebinop_ltn o1 o3.
  Proof. exact: ltn_trans. Qed.

  Lemma ebinop_eqn_ltn_gtn o1 o2 :
    (o1 == o2) || (ebinop_ltn o1 o2) || (ebinop_ltn o2 o1).
  Proof. by case: o1; case: o2. Qed.

  Definition id_bbinop (o : bbinop) : nat :=
    match o with
    | Beq => 0
    | Bult => 1
    | Bule => 2
    | Bugt => 3
    | Buge => 4
    | Bslt => 5
    | Bsle => 6
    | Bsgt => 7
    | Bsge => 8
    | Buaddo => 9
    | Busubo => 10
    | Bumulo => 11
    | Bsaddo => 12
    | Bssubo => 13
    | Bsmulo => 14
    end.

  Definition bbinop_ltn (o1 o2 : bbinop) : bool := id_bbinop o1 < id_bbinop o2.

  Lemma bbinop_ltnn o : bbinop_ltn o o = false.
  Proof. exact: ltnn. Qed.

  Lemma bbinop_ltn_eqF o1 o2 : bbinop_ltn o1 o2 -> o1 == o2 = false.
  Proof.
    move=> Hlt; apply/negP => Heq; rewrite (eqP Heq) bbinop_ltnn in Hlt; discriminate.
  Qed.

  Lemma bbinop_ltn_trans o1 o2 o3 :
    bbinop_ltn o1 o2 -> bbinop_ltn o2 o3 -> bbinop_ltn o1 o3.
  Proof. exact: ltn_trans. Qed.

  Lemma bbinop_eqn_ltn_gtn o1 o2 :
    (o1 == o2) || (bbinop_ltn o1 o2) || (bbinop_ltn o2 o1).
  Proof. by case: o1; case: o2. Qed.

  Definition id_exp (e : exp) : nat :=
    match e with
    | Evar _ => 0
    | Econst _ => 1
    | Eunop _ _ => 2
    | Ebinop _ _ _ => 3
    | Eite _ _ _ => 4
    end.

  Definition id_bexp (e : bexp) : nat :=
    match e with
    | Bfalse => 0
    | Btrue => 1
    | Bbinop _ _ _ => 2
    | Blneg _ => 3
    | Bconj _ _ => 4
    | Bdisj _ _ => 5
    end.

  Local Notation "x <? y" := (V.ltn x y).

  (* exp_ltn e1 e2 does not guarantee that the evaluation of e1 is smaller than
     the evaluation of e2 *)
  Fixpoint exp_ltn (e1 e2 : exp) : bool :=
    match e1, e2 with
    | Evar v1, Evar v2 => v1 <? v2
    | Econst n1, Econst n2 =>
      (size n1 < size n2) || ((size n1 == size n2) && (n1 <# n2)%bits)
    | Eunop o1 e1, Eunop o2 e2 =>
      eunop_ltn o1 o2 || ((o1 == o2) && (exp_ltn e1 e2))
    | Ebinop o1 e1 e2, Ebinop o2 e3 e4 =>
      ebinop_ltn o1 o2
      || ((o1 == o2) && (exp_ltn e1 e3))
      || ((o1 == o2) && (e1 == e3) && (exp_ltn e2 e4))
    | Eite c1 e1 e2, Eite c2 e3 e4 =>
      (bexp_ltn c1 c2) || ((c1 == c2) && exp_ltn e1 e3)
      || ((c1 == c2) && (e1 == e3) && exp_ltn e2 e4)
    | _, _ => id_exp e1 < id_exp e2
    end
    with
    bexp_ltn (e1 e2 : bexp) : bool :=
      match e1, e2 with
      | Bbinop o1 e1 e2, Bbinop o2 e3 e4 =>
        bbinop_ltn o1 o2
        || ((o1 == o2) && (exp_ltn e1 e3))
        || ((o1 == o2) && (e1 == e3) && (exp_ltn e2 e4))
      | Blneg e1, Blneg e2 => bexp_ltn e1 e2
      | Bconj e1 e2, Bconj e3 e4 =>
        (bexp_ltn e1 e3) || ((e1 == e3) && bexp_ltn e2 e4)
      | Bdisj e1 e2, Bdisj e3 e4 =>
        (bexp_ltn e1 e3) || ((e1 == e3) && bexp_ltn e2 e4)
      | _, _ => id_bexp e1 < id_bexp e2
      end.

  Lemma exp_ltnn (e : exp) : exp_ltn e e = false
  with bexp_ltnn (e : bexp) : bexp_ltn e e = false.
  Proof.
    (* exp_ltnn *)
    case: e => /=.
    - move=> v; exact: V.ltnn.
    - move=> b. rewrite eqxx ltBnn ltnn. reflexivity.
    - move=> o e. rewrite eunop_ltnn eqxx exp_ltnn. reflexivity.
    - move=> o e1 e2. rewrite ebinop_ltnn !eqxx (exp_ltnn e1) (exp_ltnn e2).
      reflexivity.
    - move=> b e1 e2. rewrite (bexp_ltnn b) (exp_ltnn e1) (exp_ltnn e2) !eqxx.
      reflexivity.
    (* bexp_ltnn *)
    case: e => /=.
    - rewrite ltnn. reflexivity.
    - rewrite ltnn. reflexivity.
    - move=> o e1 e2. rewrite bbinop_ltnn !eqxx (exp_ltnn e1) (exp_ltnn e2).
      reflexivity.
    - move=> b; exact: (bexp_ltnn b).
    - move=> b1 b2. rewrite (bexp_ltnn b1) (bexp_ltnn b2) eqxx. reflexivity.
    - move=> b1 b2. rewrite (bexp_ltnn b1) (bexp_ltnn b2) eqxx. reflexivity.
  Qed.

  Lemma exp_ltn_eqF (e1 e2 : exp) : exp_ltn e1 e2 -> e1 == e2 = false.
  Proof.
    move=> Hlt; apply/eqP => Heq. rewrite Heq exp_ltnn in Hlt. discriminate.
  Qed.

  Lemma bexp_ltn_eqF (e1 e2 : bexp) : bexp_ltn e1 e2 -> e1 == e2 = false.
    move=> Hlt; apply/eqP => Heq. rewrite Heq bexp_ltnn in Hlt. discriminate.
  Qed.

  Lemma exp_ltn_not_eqn (e1 e2 : exp) : exp_ltn e1 e2 -> e1 != e2.
  Proof. move=> H. rewrite (exp_ltn_eqF H). reflexivity. Qed.

  Lemma bexp_ltn_not_eqn (e1 e2 : bexp) : bexp_ltn e1 e2 -> e1 != e2.
  Proof. move=> H. rewrite (bexp_ltn_eqF H). reflexivity. Qed.

  Ltac t_auto_hook ::=
    match goal with
    | H1 : (is_true (?e1 < ?e2)),
      H2 : (is_true (?e2 < ?e3)) |- context [?e1 < ?e3] =>
      rewrite (ltn_trans H1 H2); clear H1 H2
    | H1 : (is_true (?e1 <? ?e2)),
      H2 : (is_true (?e2 <? ?e3)) |- context [(?e1 <? ?e3)] =>
      rewrite (V.ltn_trans H1 H2); clear H1 H2
    | H1 : (is_true (?e1 <# ?e2)%bits),
      H2 : (is_true (?e2 <# ?e3)%bits) |-
      context [(?e1 <# ?e3)%bits] =>
      rewrite (ltB_trans H1 H2); clear H1 H2
    | H1 : (is_true (eunop_ltn ?e1 ?e2)),
      H2 : (is_true (eunop_ltn ?e2 ?e3)) |-
      context [eunop_ltn ?e1 ?e3] =>
      rewrite (eunop_ltn_trans H1 H2); clear H1 H2
    | H1 : (is_true (ebinop_ltn ?e1 ?e2)),
      H2 : (is_true (ebinop_ltn ?e2 ?e3)) |-
      context [ebinop_ltn ?e1 ?e3] =>
      rewrite (ebinop_ltn_trans H1 H2); clear H1 H2
    | H1 : (is_true (bbinop_ltn ?e1 ?e2)),
      H2 : (is_true (bbinop_ltn ?e2 ?e3)) |-
      context [bbinop_ltn ?e1 ?e3] =>
      rewrite (bbinop_ltn_trans H1 H2); clear H1 H2
    | exp_ltn_trans :
        (forall e1 e2 e3,
            is_true (exp_ltn e1 e2) ->
            is_true (exp_ltn e2 e3) ->
            is_true (exp_ltn e1 e3)),
        H1 : is_true (exp_ltn ?e1 ?e2),
        H2 : is_true (exp_ltn ?e2 ?e3) |-
      context [exp_ltn ?e1 ?e3] =>
      rewrite (exp_ltn_trans _ _ _ H1 H2); clear H1 H2
    | bexp_ltn_trans :
        (forall e1 e2 e3,
            is_true (bexp_ltn e1 e2) ->
            is_true (bexp_ltn e2 e3) ->
            is_true (bexp_ltn e1 e3)),
        H1 : is_true (bexp_ltn ?e1 ?e2),
        H2 : is_true (bexp_ltn ?e2 ?e3) |-
      context [bexp_ltn ?e1 ?e3] =>
      rewrite (bexp_ltn_trans _ _ _ H1 H2); clear H1 H2
    end.

  Lemma exp_ltn_trans (e1 e2 e3 : exp) : exp_ltn e1 e2 -> exp_ltn e2 e3 -> exp_ltn e1 e3
  with
  bexp_ltn_trans (e1 e2 e3 : bexp) : bexp_ltn e1 e2 -> bexp_ltn e2 e3 -> bexp_ltn e1 e3.
  Proof.
    (* exp_ltn_trans *)
    case: e1.
    - move=> v1; case: e2; case: e3; try done. move=> /= *; by t_auto.
    - move=> b1; case: e2; case: e3; try done. move=> /= *; by t_auto.
    - move=> op1 ne1; case: e2; case: e3; try done. move=> /= *; by t_auto.
    - move=> op1 ne1 ne2; case: e2; case: e3; try done. move=> /= *; by t_auto.
    - move=> c1 ne1 ne2. case: e2; case: e3; try done. move=> /=*; by t_auto.
    (* bexp_ltn_trans *)
    case: e1.
    - case: e2; case: e3; try done.
    - case: e2; case: e3; try done.
    - move=> op1 ne1 ne2; case: e2; case: e3; try done. move=> /= *; by t_auto.
    - move=> ne1. case: e2; case: e3; try done. move=> /= *; by t_auto.
    - move=> ne1 ne2. case: e2; case: e3; try done. move=> /= *; by t_auto.
    - move=> ne1 ne2. case: e2; case: e3; try done. move=> /= *; by t_auto.
  Qed.

  Lemma exp_eqn_ltn_gtn (e1 e2 : exp) : (e1 == e2) || (exp_ltn e1 e2) || (exp_ltn e2 e1)
  with
  bexp_eqn_ltn_gtn (e1 e2 : bexp) : (e1 == e2) || (bexp_ltn e1 e2) || (bexp_ltn e2 e1).
  Proof.
    (* exp_eqn_ltb_gtb *)
    case: e1.
    - move=> v1; case: e2 => /=; try eauto. move=> v2.
      case: (V.compare v1 v2); rewrite /V.lt /V.eq=> H; by t_auto.
    - move=> b1; case: e2 => /=; try eauto. move=> b2.
      move: (eqn_ltn_gtn_cases (size b1) (size b2)).
      case/orP; [case/orP; [| by t_auto] | by t_auto]. move/eqP => H.
      move: (eqB_ltB_gtB_cases_ss H). by t_auto.
    - move=> op1 ne1. case: e2 => /=; try eauto. move=> op2 ne2.
      move: (eunop_eqn_ltn_gtn op1 op2) (exp_eqn_ltn_gtn ne1 ne2). by t_auto.
    - move=> op1 ne1 ne2. case: e2 => /=; try eauto. move=> op2 ne3 ne4.
      move: (ebinop_eqn_ltn_gtn op1 op2) (exp_eqn_ltn_gtn ne1 ne3)
                                         (exp_eqn_ltn_gtn ne2 ne4).
      by t_auto.
    - move=> b1 ne1 ne2. case: e2 => /=; try eauto. move=> b2 ne3 ne4.
      move: (bexp_eqn_ltn_gtn b1 b2) (exp_eqn_ltn_gtn ne1 ne3)
                                     (exp_eqn_ltn_gtn ne2 ne4).
      by t_auto.
    (* bexp_eq_lt_gt *)
    case: e1.
    - case: e2 => /=; try eauto.
    - case: e2 => /=; try eauto.
    - move=> op1 ne1 ne2. case: e2 => /=; try eauto. move=> op2 ne3 ne4.
      move: (bbinop_eqn_ltn_gtn op1 op2) (exp_eqn_ltn_gtn ne1 ne3)
                                         (exp_eqn_ltn_gtn ne2 ne4).
      by t_auto.
    - move=> b1. case: e2 => /=; try eauto. move=> b2.
      move: (bexp_eqn_ltn_gtn b1 b2). by t_auto.
    - move=> b1 b2. case: e2 => /=; try eauto. move=> b3 b4.
      move: (bexp_eqn_ltn_gtn b1 b3) (bexp_eqn_ltn_gtn b2 b4). by t_auto.
    - move=> b1 b2. case: e2 => /=; try eauto. move=> b3 b4.
      move: (bexp_eqn_ltn_gtn b1 b3) (bexp_eqn_ltn_gtn b2 b4). by t_auto.
  Qed.

  Fixpoint exp_compare (e1 e2 : exp) : Compare exp_ltn eq_op e1 e2
  with bexp_compare (e1 e2 : bexp) : Compare bexp_ltn eq_op e1 e2.
  Proof.
    (* exp_compare *)
    move: (exp_eqn_ltn_gtn e1 e2). case H: (e1 == e2) => /=.
    - move=> _. apply: EQ. exact: H.
    - move=> {H}. case H: (exp_ltn e1 e2) => /=.
      + move=> _. apply: LT. exact: H.
      + move=> {H} H. apply: GT. exact: H.
    (* bexp_compare *)
    move: (bexp_eqn_ltn_gtn e1 e2). case H: (e1 == e2) => /=.
    - move=> _. apply: EQ. exact: H.
    - move=> {H}. case H: (bexp_ltn e1 e2) => /=.
      + move=> _. apply: LT. exact: H.
      + move=> {H} H. apply: GT. exact: H.
  Defined.

  (* exp and bexp are ordered *)
  Module ExpOrderMinimal <: EqOrderMinimal.
    Definition t := exp_eqType.
    Definition eqn (e1 e2 : t) : bool := e1 == e2.
    Definition ltn (e1 e2 : t) : bool := exp_ltn e1 e2.
    Lemma ltn_trans : forall (e1 e2 e3 : t), ltn e1 e2 -> ltn e2 e3 -> ltn e1 e3.
    Proof. exact: exp_ltn_trans. Qed.
    Lemma ltn_not_eqn (e1 e2 : t) : ltn e1 e2 -> e1 != e2.
    Proof. exact: exp_ltn_not_eqn. Qed.
    Definition compare (e1 e2 : t) : Compare ltn eqn e1 e2 := exp_compare e1 e2.
  End ExpOrderMinimal.

  Module ExpOrder <: EqOrder := MakeEqOrder ExpOrderMinimal.

  Module BexpOrderMinimal <: EqOrderMinimal.
    Definition t := bexp_eqType.
    Definition eqn (e1 e2 : t) : bool := e1 == e2.
    Definition ltn (e1 e2 : t) : bool := bexp_ltn e1 e2.
    Lemma ltn_trans : forall (e1 e2 e3 : t), ltn e1 e2 -> ltn e2 e3 -> ltn e1 e3.
    Proof. exact: bexp_ltn_trans. Qed.
    Lemma ltn_not_eqn (e1 e2 : t) : ltn e1 e2 -> e1 != e2.
    Proof. exact: bexp_ltn_not_eqn. Qed.
    Definition compare (e1 e2 : t) : Compare ltn eqn e1 e2 := bexp_compare e1 e2.
  End BexpOrderMinimal.

  Module BexpOrder <: EqOrder := MakeEqOrder BexpOrderMinimal.


  (* Subexpression *)

  Section Subexp.

    Fixpoint len_exp (e : exp) : nat :=
      match e with
      | Evar v => 1
      | Econst n => 1
      | Eunop op e => (len_exp e).+1
      | Ebinop op e1 e2 => (len_exp e1 + len_exp e2).+1
      | Eite b e1 e2 => (len_bexp b + len_exp e1 + len_exp e2).+1
      end
    with
    len_bexp (e : bexp) : nat :=
      match e with
      | Bfalse => 1
      | Btrue => 1
      | Bbinop op e1 e2 => (len_exp e1 + len_exp e2).+1
      | Blneg e => (len_bexp e).+1
      | Bconj e1 e2
      | Bdisj e1 e2 => (len_bexp e1 + len_bexp e2).+1
      end.

    Fixpoint subee (c : exp) (p : exp) {struct p} : bool :=
      (c == p) || (
                 match p with
                 | Evar _
                 | Econst _ => false
                 | Eunop op e => subee c e
                 | Ebinop op e1 e2 => subee c e1 || subee c e2
                 | Eite b e1 e2 => subeb c b || subee c e1 || subee c e2
                 end
               )
    with
    subeb (e : exp) (b : bexp) {struct b} : bool :=
      match b with
      | Bfalse
      | Btrue => false
      | Bbinop op e1 e2 => subee e e1 || subee e e2
      | Blneg b => subeb e b
      | Bconj b1 b2
      | Bdisj b1 b2 => subeb e b1 || subeb e b2
      end.

    Fixpoint subbe (c : bexp) (p : exp) {struct p} : bool :=
      match p with
      | Evar _
      | Econst _ => false
      | Eunop op e => subbe c e
      | Ebinop op e1 e2 => subbe c e1 || subbe c e2
      | Eite b e1 e2 => subbb c b || subbe c e1 || subbe c e2
      end
    with subbb (c p : bexp) {struct p} : bool :=
           (c == p) ||
                    match p with
                    | Bfalse
                    | Btrue => false
                    | Bbinop _ e1 e2 => subbe c e1 || subbe c e2
                    | Blneg b => subbb c b
                    | Bconj b1 b2
                    | Bdisj b1 b2 => subbb c b1 || subbb c b2
                    end.

    Lemma subee_refl e : subee e e.
    Proof. case: e => * /=; by rewrite eqxx. Qed.

    Lemma subbb_refl e : subbb e e.
    Proof. case: e => * /=; by rewrite ?eqxx. Qed.

    (* We need to simplify the term before applying induction hypotheses.
     Otherwise, induction hypotheses will be applied using the same terms. *)
    Ltac t_auto_first ::= simpl.
    Ltac t_auto_hook ::=
      match goal with
      | H1 : (forall e1 e2,
                 is_true (subee e1 e2) -> is_true (len_exp e1 <= len_exp e2)),
             H2 : is_true (subee ?e1 ?e2)
        |- _ =>
        move: (H1 _ _ H2); clear H2; simpl; intro H2
      | H1 : (forall e1 e2,
                 is_true (subeb e1 e2) -> is_true (len_exp e1 <= len_bexp e2)),
             H2 : is_true (subeb ?e1 ?e2)
        |- _ =>
        move: (H1 _ _ H2); clear H2; simpl; intro H2
      | H1 : (forall e1 e2,
                 is_true (subbe e1 e2) -> is_true (len_bexp e1 <= len_exp e2)),
             H2 : is_true (subbe ?e1 ?e2)
        |- _ =>
        move: (H1 _ _ H2); clear H2; simpl; intro H2
      | H1 : (forall e1 e2,
                 is_true (subbb e1 e2) -> is_true (len_bexp e1 <= len_bexp e2)),
             H2 : is_true (subbb ?e1 ?e2)
        |- _ =>
        move: (H1 _ _ H2); clear H2; simpl; intro H2
      | |- is_true (0 < _.+1) => exact: ltn0Sn
      | |- is_true (?a < ?a.+1) => exact: leqnn
      | H : is_true (?a < _) |- is_true (?a < _.+1) => apply: (ltn_trans H)
      | |- is_true (?a < (?a + _).+1) => exact: leq_addr
      | |- is_true (?a < (_ + ?a).+1) => exact: leq_addl
      | |- is_true (?a < (?a + _ + _).+1) => rewrite -addnA; exact: leq_addr
      | |- is_true (?a < (?b + ?a + _).+1) => rewrite (addnC b) -addnA; exact: leq_addr
      end.

    Lemma subee_len e1 e2 : subee e1 e2 -> len_exp e1 <= len_exp e2
    with subeb_len e b : subeb e b -> len_exp e <= len_bexp b.
    Proof.
      (* subee_len *)
      case: e1.
      - move=> ?; case: e2 => //=.
      - move=> ?; case: e2 => //=.
      - move=> ? ?; case: e2; by t_auto.
      - move=> ? ? ?; case: e2; by t_auto.
      - move=> ? ? ?; case: e2; by t_auto.
        (* subeb_len *)
        case: e.
      - move=> ?; case: b => //=.
      - move=> ?; case: b => //=.
      - move=> ? ?; case: b; by t_auto.
      - move=> ? ? ?; case: b; by t_auto.
      - move=> ? ? ?; case: b; by t_auto.
    Qed.

    Lemma subbe_len b e : subbe b e -> len_bexp b <= len_exp e
    with subbb_len b1 b2 : subbb b1 b2 -> len_bexp b1 <= len_bexp b2.
    Proof.
      (* subbe_len *)
      case: b.
      - case: e; by t_auto.
      - case: e; by t_auto.
      - move=> ? ? ?; case: e; by t_auto.
      - move=> ?; case: e; by t_auto.
      - move=> ? ?; case: e; by t_auto.
      - move=> ? ?; case: e; by t_auto.
        (* subbb_len *)
        case: b1.
      - case: b2; by t_auto.
      - case: b2; by t_auto.
      - move=> ? ? ?; case: b2; by t_auto.
      - move=> ?; case: b2; by t_auto.
      - move=> ? ?; case: b2; by t_auto.
      - move=> ? ?; case: b2; by t_auto.
    Qed.

    (* case selection *)
    Ltac subexp_trans_select :=
      match goal with
      | H1 : is_true (?f ?e1 _),
             H2 : is_true (?g _ ?e3) |-
        is_true (?h ?e1 ?e3 || _) => leftb
      | H1 : is_true (?f ?e1 _),
             H2 : is_true (?g _ ?e3) |-
        is_true (_ || ?h ?e1 ?e3) => rightb

      | H1 : is_true (?f ?e1 _),
             H2 : is_true (?g _ ?e3) |-
        is_true (_ || ?h ?e1 ?e3 || _) => leftb; rightb
      | H1 : is_true (?f ?e1 _),
             H2 : is_true (?g _ ?e3) |-
        is_true (?h ?e1 ?e3 || _ || _) => leftb; leftb
      | H1 : is_true (?f ?e1 _),
             H2 : is_true (?g _ ?e3) |-
        is_true (_ || (?h ?e1 ?e3 || _)) => rightb; leftb
      | H1 : is_true (?f ?e1 _),
             H2 : is_true (?g _ ?e3) |-
        is_true (_ || (_ || ?h ?e1 ?e3)) => rightb; rightb

      | H1 : is_true (?f ?e1 _),
             H2 : is_true (?g _ ?e3) |-
        is_true [|| _, _ || ?h ?e1 ?e3 | _] => rightb; leftb; rightb
      | H1 : is_true (?f ?e1 _),
             H2 : is_true (?g _ ?e3) |-
        is_true [|| _, ?h ?e1 ?e3 || _ | _] => rightb; leftb; leftb
      | H1 : is_true (?f _ ?e3),
             H2 : is_true (?g ?e1 _) |-
        is_true [|| _, _ || ?h ?e1 ?e3 | _] => rightb; rightb
      | H1 : is_true (?f ?e1 _),
             H2 : is_true (?g _ ?e3) |-
        is_true [|| _, ?h ?e1 ?e3 || _ | _] => rightb; leftb; leftb
      end.

    (* Simplify goal after applying induction hypotheses so that induction hypotheses
     won't be applied with the same term. The order of the cases is important. *)
    Ltac subexp_trans_app :=
      match goal with
      | subeeee_trans :
          (forall e1 e2 e3 : exp,
              is_true (subee e1 e2) -> is_true (subee e2 e3) -> is_true (subee e1 e3)),
          H : is_true (subee ?e2 ?e3) |-
        is_true (subee ?e1 ?e3) =>
        apply: (subeeee_trans _ _ _ _ H); clear H; simpl
      | subbbbb_trans :
          (forall b1 b2 b3 : bexp,
              is_true (subbb b1 b2) -> is_true (subbb b2 b3) -> is_true (subbb b1 b3)),
          H : is_true (subbb ?b2 ?b3) |-
        is_true (subbb ?b1 ?b3) =>
        apply: (subbbbb_trans _ _ _ _ H); clear H; simpl
      | subeeeb_trans :
          (forall (e1 e2 : exp) (b : bexp),
              is_true (subee e1 e2) -> is_true (subeb e2 b) -> is_true (subeb e1 b)),
          H : is_true (subeb ?e2 ?e3) |-
        is_true (subeb ?e1 ?e3) =>
        apply: (subeeeb_trans _ _ _ _ H); clear H; simpl
      | subbeee_trans :
          (forall (b : bexp) (e1 e2 : exp),
              is_true (subbe b e1) -> is_true (subee e1 e2) -> is_true (subbe b e2)),
          H : is_true (subee ?e2 ?e3) |-
        is_true (subbe ?e1 ?e3) =>
        apply: (subbeee_trans _ _ _ _ H); clear H; simpl
      | subbeeb_trans :
          (forall (b1 : bexp) (e : exp) (b2 : bexp),
              is_true (subbe b1 e) -> is_true (subeb e b2) -> is_true (subbb b1 b2)),
          H : is_true (subeb ?e2 ?e3) |-
        is_true (subbb ?e1 ?e3) =>
        apply: (subbeeb_trans _ _ _ _ H); clear H; simpl
      | subebbe_trans :
          (forall (e1 : exp) (b : bexp) (e2 : exp),
              is_true (subeb e1 b) -> is_true (subbe b e2) -> is_true (subee e1 e2)),
          H : is_true (subbe ?e2 ?e3) |-
        is_true (subee ?e1 ?e3) =>
        apply: (subebbe_trans _ _ _ _ H); clear H; simpl
      | subebbb_trans :
          (forall (e : exp) (b1 b2 : bexp),
              is_true (subeb e b1) -> is_true (subbb b1 b2) -> is_true (subeb e b2)),
          H : is_true (subbb ?e2 ?e3) |-
        is_true (subeb ?e1 ?e3) =>
        apply: (subebbb_trans _ _ _ _ H); clear H; simpl
      | subbbbe_trans :
          (forall (b1 b2 : bexp) (e : exp),
              is_true (subbb b1 b2) -> is_true (subbe b2 e) -> is_true (subbe b1 e)),
          H : is_true (subbe ?e2 ?e3) |-
        is_true (subbe ?e1 ?e3) =>
        apply: (subbbbe_trans _ _ _ _ H); clear H; simpl
      | subeeee_trans :
          (forall e1 e2 e3 : exp,
              is_true (subee e1 e2) -> is_true (subee e2 e3) -> is_true (subee e1 e3)),
          H : is_true (subee ?e1 ?e2) |-
        is_true (subee ?e1 ?e3) =>
        apply: (subeeee_trans _ _ _ H); clear H; simpl
      | subbbbb_trans :
          (forall b1 b2 b3 : bexp,
              is_true (subbb b1 b2) -> is_true (subbb b2 b3) -> is_true (subbb b1 b3)),
          H : is_true (subbb ?b1 ?b2) |-
        is_true (subbb ?b1 ?b3) =>
        apply: (subbbbb_trans _ _ _ H); clear H; simpl
      end.

    (* final decision *)
    Ltac subexp_trans_decide :=
      match goal with
      | |- is_true (subee ?e ?e) => exact: subee_refl
      | |- is_true (subee ?e (?f ?e)) =>
        apply/orP; right; exact: subee_refl
      | |- is_true (subee ?e (?f ?e _)) =>
        apply/orP; right; apply/orP; left; exact: subee_refl
      | |- is_true (subee ?e (?f _ ?e)) =>
        apply/orP; right; apply/orP; right; exact: subee_refl
      | H : is_true (subeb ?e ?b) |-
        is_true (subee ?e (?f ?b _ _)) =>
        apply/orP; right; apply/orP; left; apply/orP; left; exact: H
      | |- is_true (subee ?e (?f _ ?e _)) =>
        apply/orP; right; apply/orP; left; apply/orP; right; exact: subee_refl
      | |- is_true (subee ?e (?f _ _ ?e)) =>
        apply/orP; right; apply/orP; right; exact: subee_refl
      end.

    Ltac t_auto_hook ::= (subexp_trans_select || subexp_trans_app || subexp_trans_decide).

    Lemma subeeee_trans e1 e2 e3 : subee e1 e2 -> subee e2 e3 -> subee e1 e3
    with
    subeeeb_trans e1 e2 b : subee e1 e2 -> subeb e2 b -> subeb e1 b.
    Proof.
      (* subeeee_trans *)
      case: e1.
      - move=> ?; case: e2; case: e3; by t_auto.
      - move=> b; case: e2; case: e3; by t_auto.
      - move=> e; case: e2; case: e3; by t_auto.
      - move=> ne1 ne2; case: e2; case: e3; by t_auto.
      - move=> b1 ne1 ne2; case: e2; case: e3; by t_auto.
        (* subeeeb_trans *)
        case: e1 => /=.
      - move=> v; case: e2; case: b; by t_auto.
      - move=> bs; case: e2; case: b; by t_auto.
      - move=> op1 ne1; case: e2; case: b; by t_auto.
      - move=> ne1 ne2; case: e2; case: b; by t_auto.
      - move=> b1 ne1 ne2; case: e2; case: b; by t_auto.
    Qed.

    Lemma subbeee_trans b e1 e2 : subbe b e1 -> subee e1 e2 -> subbe b e2
    with
    subebbe_trans e1 b e2 : subeb e1 b -> subbe b e2 -> subee e1 e2
    with
    subbeeb_trans b1 e b2 : subbe b1 e -> subeb e b2 -> subbb b1 b2
    with
    subebbb_trans e b1 b2 : subeb e b1 -> subbb b1 b2 -> subeb e b2
    with
    subbbbe_trans b1 b2 e : subbb b1 b2 -> subbe b2 e -> subbe b1 e
    with
    subbbbb_trans b1 b2 b3 : subbb b1 b2 -> subbb b2 b3 -> subbb b1 b3.
    Proof.
      (* subbeee_trans *)
      case: b.
      - case: e1; case: e2; by t_auto.
      - case: e1; case: e2; by t_auto.
      - move=> ? ? ?; case: e1; case: e2; by t_auto.
      - move=> ?; case: e1; case: e2; by t_auto.
      - move=> ? ?; case: e1; case: e2; by t_auto.
      - move=> ? ?; case: e1; case: e2; by t_auto.
        (* subebbe_trans *)
        case: e1.
      - move=> ?; case: b; case: e2; by t_auto.
      - move=> ?; case: b; case: e2; by t_auto.
      - move=> ? ?; case: b; case: e2; by t_auto.
      - move=> ? ? ?; case: b; case: e2; by t_auto.
      - move=> ? ? ?; case: b; case: e2; by t_auto.
        (* subbeeb_trans *)
        case: b1.
      - case: e; case: b2; by t_auto.
      - case: e; case: b2; by t_auto.
      - move=> ? ? ?; case: e; case: b2; by t_auto.
      - move=> ?; case: e; case: b2; by t_auto.
      - move=> ? ?; case: e; case: b2; by t_auto.
      - move=> ? ?; case: e; case: b2; by t_auto.
        (* subebbb_trans *)
        case: e.
      - move=> ?; case: b1; case: b2; by t_auto.
      - move=> ?; case: b1; case: b2; by t_auto.
      - move=> ? ?; case: b1; case: b2; by t_auto.
      - move=> ? ? ?; case: b1; case: b2; by t_auto.
      - move=> ? ? ?; case: b1; case: b2; by t_auto.
        (* subbbbe_trans *)
        case: b1.
      - case: b2; case: e; by t_auto.
      - case: b2; case: e; by t_auto.
      - move=> ? ? ?; case: b2; case: e; by t_auto.
      - move=> ?; case: b2; case: e; by t_auto.
      - move=> ? ?; case: b2; case: e; by t_auto.
      - move=> ? ?; case: b2; case: e; by t_auto.
        (* subbbbb_trans *)
        case: b1.
      - case: b2; case: b3; by t_auto.
      - case: b2; case: b3; by t_auto.
      - move=> ? ? ?; case: b2; case: b3; by t_auto.
      - move=> ?; case: b2; case: b3; by t_auto.
      - move=> ? ?; case: b2; case: b3; by t_auto.
      - move=> ? ?; case: b2; case: b3; by t_auto.
    Qed.

    Ltac t_auto_hook ::=
      (* Turn a contradiction on subee (subbb etc.) to a contradiction on lt of nat. *)
      match goal with
      | H1 : is_true (?subf ?p1 ?e1),
             H2 : is_true (?subg ?p2 ?e2)
        |- _ =>
        match p1 with
        | context [e2] =>
          match p2 with
          | context [e1] =>
            let sf := match subf with
                      | subee => subee_len
                      | subeb => subeb_len
                      | subbe => subbe_len
                      | subbb => subbb_len
                      end in
            let sg := match subg with
                      | subee => subee_len
                      | subeb => subeb_len
                      | subbe => subbe_len
                      | subbb => subbb_len
                      end in
            move: (sf _ _ H1) (sg _ _ H2); simpl; clear H1 H2; intros H1 H2
          end
        end
      | H1 : is_true (?a < ?b), H2 : is_true (?b < ?a) |- _ =>
        move: (ltn_trans H1 H2); by rewrite ltnn
      | H1 : is_true (?a < ?b), H2 : is_true (?b + ?c < ?a) |- _ =>
        move: (ltn_leq_trans H1 (leq_addr c b)); clear H1; intro H1;
        move: (ltn_trans H1 H2); by rewrite ltnn
      | H1 : is_true (?a < ?b), H2 : is_true (?c + ?b < ?a) |- _ =>
        move: (ltn_leq_trans H1 (leq_addl c b)); clear H1; intro H1;
        move: (ltn_trans H1 H2); by rewrite ltnn
      | H1 : is_true (?a < ?b), H2 : is_true (?b + ?c + ?d < ?a) |- _ =>
        move: (ltn_leq_trans H1 (leq_addr (c + d) b)); clear H1; rewrite addnA; intro H1;
        move: (ltn_trans H1 H2); by rewrite ltnn
      | H1 : is_true (?a < ?b), H2 : is_true (?c + ?b + ?d < ?a) |- _ =>
        move: (ltn_leq_trans H1 (leq_addl c b)); clear H1; intro H1;
        move: (ltn_leq_trans H1 (leq_addr d (c + b))); clear H1; intro H1;
        move: (ltn_trans H1 H2); by rewrite ltnn
      | H1 : is_true (?a + ?c < ?b),
             H2 : is_true (?b + ?d < ?a)
        |- _ =>
        let H := fresh in
        move: (leq_addr d b); intro H;
        move: (leq_ltn_trans H H2); clear H H2; intro H;
        move: (ltn_addr c H) => {H} H;
                                move: (ltn_trans H H1); by rewrite ltnn
      | H1 : is_true (?a + ?c < ?b),
             H2 : is_true (?d + ?b < ?a)
        |- _ => rewrite (addnC d b) in H2
      | H1 : is_true (?c + ?a < ?b),
             H2 : is_true (?d + ?b < ?a)
        |- _ => rewrite (addnC c a) in H1; rewrite (addnC d b) in H2
      | H1 : is_true (?a + ?c < ?b),
             H2 : is_true (?b + ?d + ?e < ?a)
        |- _ =>
        let H := fresh in
        move: (leq_addr (d + e) b); rewrite addnA; intro H;
        move: (ltn_leq_trans H1 H); clear H1 H; intro H;
        move: (ltn_trans H H2); clear H H2; intro H;
        move: (ltn_addr c H); by rewrite ltnn
      | H1 : is_true (?a + ?c < ?b),
             H2 : is_true (?d + ?b + ?e < ?a)
        |- _ => rewrite (addnC d b) in H2
      | H1 : is_true (?c + ?a < ?b),
             H2 : is_true (?b + ?d + ?e < ?a)
        |- _ => rewrite (addnC c a) in H1
      | H1 : is_true (?c + ?a < ?b),
             H2 : is_true (?d + ?b + ?e < ?a)
        |- _ => rewrite (addnC c a) in H1; rewrite (addnC d b) in H2
      | H1 : is_true (?a + ?c + ?d < ?b),
             H2 : is_true (?b + ?e + ?f < ?a)
        |- _ =>
        let Hi := fresh in
        let Hj := fresh in
        move: (leq_addr (c + d) a); rewrite addnA; intro Hi;
        move: (leq_addr (e + f) b); rewrite addnA; intro Hj;
        move: (leq_ltn_trans Hi H1); clear Hi H1; intro Hi;
        move: (leq_ltn_trans Hj H2); clear Hj H2; intro Hj;
        move: (ltn_trans Hi Hj); by rewrite ltnn
      | H1 : is_true (?c + ?a + ?d < ?b),
             H2 : is_true (?b + ?e + ?f < ?a)
        |- _ => rewrite (addnC c a) in H1
      | H1 : is_true (?c + ?a + ?d < ?b),
             H2 : is_true (?e + ?b + ?f < ?a)
        |- _ => rewrite (addnC c a) in H1; rewrite (addnC e b) in H2
      end.

    Lemma subee_antisym c p : (subee c p && subee p c) = (c == p).
    Proof.
      case H: (c == p).
      - rewrite (eqP H). by rewrite subee_refl.
      - apply/negP => Hsub. apply/negPf: H. case/andP: Hsub.
        elim: c p.
      - move=> ?; case; by t_auto.
      - move=> ?; case; by t_auto.
      - move=> ? ? ?; case; by t_auto.
      - move=> ? ? ? ? ?; case; by t_auto.
      - move=> ? ? ? ? ?; case; by t_auto.
    Qed.

    Lemma subbb_antisym c p : (subbb c p && subbb p c) = (c == p).
    Proof.
      case H: (c == p).
      - rewrite (eqP H). by rewrite subbb_refl.
      - apply/negP => Hsub. apply/negPf: H. case/andP: Hsub.
        elim: c p.
      - case; by t_auto.
      - case; by t_auto.
      - move=> ? ? ?; case; by t_auto.
      - move=> ? ?; case; by t_auto.
      - move=> ? ? ? ?; case; by t_auto.
      - move=> ? ? ? ?; case; by t_auto.
    Qed.

    (* subexp and variables in expressions *)

    Ltac subexp_vars_select :=
      subexp_trans_select
      || (match goal with
          | |- is_true (_ || ?f ?e ?e) => apply/orP; right
          | |- is_true (?f ?e ?e || _ || _) => apply/orP; left; apply/orP; left
          | |- is_true ([|| _, ?f ?e ?e | _]) => apply/orP; right; apply/orP; left
          | |- is_true ([|| _, _ | ?f ?e ?e]) => apply/orP; right; apply/orP; right
          | |- is_true ([|| _, _ || ?f ?e ?e | _]) =>
            apply/orP; right; apply/orP; left; apply/orP; right
          | |- is_true (VS.subset ?e (VS.union ?e _)) => apply: VSLemmas.subset_union1
          | |- is_true (VS.subset ?e (VS.union _ ?e)) => apply: VSLemmas.subset_union2
          | H : is_true (?sub _ ?e) |- is_true (VS.subset _ (VS.union (?vars ?e) _)) =>
            apply: VSLemmas.subset_union1
          | H : is_true (?sub _ ?e) |- is_true (VS.subset _ (VS.union _ (?vars ?e))) =>
            apply: VSLemmas.subset_union2
          | H : is_true (?sub _ ?e) |-
            is_true (VS.subset _ (VS.union (?vars ?e) (VS.union _ _))) =>
            apply: VSLemmas.subset_union1
          | H : is_true (?sub _ ?e) |-
            is_true (VS.subset _ (VS.union _ (VS.union (?vars ?e) _))) =>
            apply: VSLemmas.subset_union2; apply: VSLemmas.subset_union1
          | H : is_true (?sub _ ?e) |-
            is_true (VS.subset _ (VS.union _ (VS.union _ (?vars ?e)))) =>
            apply: VSLemmas.subset_union2; apply: VSLemmas.subset_union2
          | |- is_true (VS.subset (VS.union _ _) _) =>
            apply: VSLemmas.subset_union3
          end).

    Ltac subexp_vars_app :=
      match goal with
      | H : is_true (subee ?e2 ?e3) |- is_true (subee ?e1 ?e3) =>
        apply: (subeeee_trans _ H); clear H; simpl
      | H : is_true (subbb ?b2 ?b3) |- is_true (subbb ?b1 ?b3) =>
        apply: (subbbbb_trans _ H); clear H; simpl
      | H : is_true (subeb ?e2 ?e3) |- is_true (subeb ?e1 ?e3) =>
        apply: (subeeeb_trans _ H); clear H; simpl
      | H : is_true (subee ?e2 ?e3) |- is_true (subbe ?e1 ?e3) =>
        apply: (subbeee_trans _ H); clear H; simpl
      | H : is_true (subeb ?e2 ?e3) |- is_true (subbb ?e1 ?e3) =>
        apply: (subbeeb_trans _ H); clear H; simpl
      | H : is_true (subbe ?e2 ?e3) |- is_true (subee ?e1 ?e3) =>
        apply: (subebbe_trans _ H); clear H; simpl
      | H : is_true (subbb ?e2 ?e3) |- is_true (subeb ?e1 ?e3) =>
        apply: (subebbb_trans _ H); clear H; simpl
      | H : is_true (subbe ?e2 ?e3) |- is_true (subbe ?e1 ?e3) =>
        apply: (subbbbe_trans _ H); clear H; simpl
      | H : is_true (subee ?e1 ?e2) |- is_true (subee ?e1 ?e3) =>
        apply: (subeeee_trans H); clear H; simpl
      | H : is_true (subbb ?b1 ?b2) |- is_true (subbb ?b1 ?b3) =>
        apply: (subbbbb_trans H); clear H; simpl
      | subee_vars_subset :
          (forall e1 e2 : exp,
              is_true (subee e1 e2) -> is_true (VS.subset (vars_exp e1) (vars_exp e2))),
          H : is_true (subee _ ?e)
        |- is_true (VS.subset (VS.singleton ?v) (vars_exp ?e)) =>
        replace (VS.singleton v) with (vars_exp (Evar v)) by reflexivity;
        apply: subee_vars_subset
      | subee_vars_subset :
          (forall e1 e2 : exp,
              is_true (subee e1 e2) -> is_true (VS.subset (vars_exp e1) (vars_exp e2))),
          H : is_true (subee _ ?e)
        |- is_true (VS.subset (vars_exp _) (vars_exp ?e)) =>
        apply: subee_vars_subset
      | subeb_vars_subset :
          (forall (e1 : exp) (e2 : bexp),
              is_true (subeb e1 e2) -> is_true (VS.subset (vars_exp e1) (vars_bexp e2))),
          H : is_true (subeb _ ?e)
        |- is_true (VS.subset (VS.singleton ?v) (vars_bexp ?e)) =>
        replace (VS.singleton v) with (vars_exp (Evar v)) by reflexivity;
        apply: subeb_vars_subset
      | subeb_vars_subset :
          (forall (e1 : exp) (e2 : bexp),
              is_true (subeb e1 e2) -> is_true (VS.subset (vars_exp e1) (vars_bexp e2))),
          H : is_true (subeb _ ?e)
        |- is_true (VS.subset (vars_exp _) (vars_bexp ?e)) =>
        apply: subeb_vars_subset
      | subbe_vars_subset :
          (forall (b : bexp) (e : exp),
              is_true (subbe b e) -> is_true (VS.subset (vars_bexp b) (vars_exp e))),
          H : is_true (subee _ ?e)
        |- is_true (VS.subset (vars_bexp _) (vars_exp ?e)) =>
        apply: subbe_vars_subset
      | subbb_vars_subset :
          (forall b1 b2 : bexp,
              is_true (subbb b1 b2) ->
              is_true (VS.subset (vars_bexp b1) (vars_bexp b2))),
          H : is_true (subeb _ ?e)
        |- is_true (VS.subset _ (vars_bexp ?e)) =>
        apply: subbb_vars_subset
      end.

    Ltac subexp_vars_decide :=
      subexp_trans_decide
      || (match goal with
          | |- is_true (VS.subset VS.empty ?vs) => exact: VSLemmas.subset_empty
          | |- is_true (VS.subset ?vs ?vs) => exact: VSLemmas.subset_refl
          | |- is_true (subee ?e ?e) => exact: subee_refl
          | |- is_true (subbb ?e ?e) => exact: subbb_refl
          end).

    Ltac t_auto_hook ::= (subexp_vars_select || subexp_vars_app || subexp_vars_decide).

    Lemma subee_vars_subset e1 e2 : subee e1 e2 -> VS.subset (vars_exp e1) (vars_exp e2)
    with
    subeb_vars_subset e b : subeb e b -> VS.subset (vars_exp e) (vars_bexp b)
    with
    subbe_vars_subset b e : subbe b e -> VS.subset (vars_bexp b) (vars_exp e)
    with
    subbb_vars_subset b1 b2 : subbb b1 b2 -> VS.subset (vars_bexp b1) (vars_bexp b2).
    Proof.
      (* subee_vars_subset *)
      case: e1; case: e2 => //=; try by t_auto.
      (* subeb_vars_subset *)
      (* subbe_vars_subset *)
      (* subbb_vars_subset *)
    Abort.

  End Subexp.


  (* Well-formedness *)

  From ssrlib Require Import EqFMaps.

  Module TELemmas := FMapLemmas TE.

  Section WellFormed.

    Fixpoint exp_size (e : exp) (te : TE.env) : nat :=
      match e with
      | Evar v => TE.vsize v te
      | Econst n => size n
      | Eunop op e =>
        (match op with
         | Unot => exp_size e te
         | Uneg => exp_size e te
         | Uextr i j => i - j + 1
         (*     | Uslice w1 w2 w3 => w2 *)
         | Uhigh n => n
         | Ulow n => n
         | Uzext n => exp_size e te + n
         | Usext n => exp_size e te + n
         | Urepeat n => n * exp_size e te
         | Urotl n => exp_size e te
         | Urotr n => exp_size e te
         end)
      | Ebinop op e1 e2 =>
        (match op with
         | Band | Bor | Bxor => maxn (exp_size e1 te) (exp_size e2 te)
         | Badd | Bsub => minn (exp_size e1 te) (exp_size e2 te)
         | Bmul => exp_size e1 te
         | Bdiv => exp_size e1 te
         | Bmod => exp_size e1 te
         | Bsdiv => exp_size e1 te
         | Bsrem => exp_size e1 te
         | Bsmod => exp_size e1 te (* TODO: size_smodB is not fixed *)
         | Bshl | Blshr | Bashr => exp_size e1 te
         | Bconcat => exp_size e1 te + exp_size e2 te
         | Bcomp => 1
         end)
      | Eite b e1 e2 => maxn (exp_size e1 te) (exp_size e2 te)
      end.

    Fixpoint well_formed_exp (e : exp) (te : TE.env) : bool :=
      match e with
      | Evar v => TE.mem v te
      | Econst _ => true
      | Eunop op e => well_formed_exp e te
      | Ebinop op e1 e2 =>
        well_formed_exp e1 te && well_formed_exp e2 te &&
                        (0 < exp_size e1 te) &&
                        (if op == Bconcat then true
                         else exp_size e1 te == exp_size e2 te)
      | Eite b e1 e2 =>
        well_formed_bexp b te && well_formed_exp e1 te && well_formed_exp e2 te &&
                         (exp_size e1 te == exp_size e2 te)
      end
    with
    well_formed_bexp (b : bexp) (te : TE.env) : bool :=
      match b with
      | Bfalse
      | Btrue => true
      | Bbinop _ e1 e2 => well_formed_exp e1 te && well_formed_exp e2 te &&
                                          (exp_size e1 te == exp_size e2 te)
      | Blneg b => well_formed_bexp b te
      | Bconj b1 b2
      | Bdisj b1 b2 => well_formed_bexp b1 te && well_formed_bexp b2 te
      end.

    Definition well_formed_bexps (bs : seq bexp) (E : TE.env) : bool :=
      all (well_formed_bexp^~E) bs.

    Lemma well_formed_bexps_cons E e es :
      well_formed_bexps (e::es) E = well_formed_bexp e E && well_formed_bexps es E.
    Proof. reflexivity. Qed.

    Lemma well_formed_bexps_cat E es1 es2 :
      well_formed_bexps (es1 ++ es2) E =
      well_formed_bexps es1 E && well_formed_bexps es2 E.
    Proof.
      elim: es1 es2 => [| e1 es1 IH] es2 //=. rewrite IH. rewrite andbA.
      reflexivity.
    Qed.

    Lemma well_formed_bexps_rcons E es e :
      well_formed_bexps (rcons es e) E =
      well_formed_bexps es E && well_formed_bexp e E.
    Proof.
      elim: es => [| hd tl IH] //=.
      - rewrite andbT. reflexivity.
      - rewrite IH. rewrite andbA. reflexivity.
    Qed.

    Lemma well_formed_bexps_rev E es :
      well_formed_bexps (rev es) E = well_formed_bexps es E.
    Proof.
      elim: es => [| e es IH] //=. rewrite rev_cons well_formed_bexps_rcons.
      rewrite IH andbC. reflexivity.
    Qed.

    Lemma well_formed_bexps_flatten E ess :
      well_formed_bexps (flatten ess) E = all (well_formed_bexps^~E) ess.
    Proof.
      rewrite /well_formed_bexps /=. rewrite all_flatten. reflexivity.
    Qed.

    Lemma well_formed_bexps_tflatten E ess :
      well_formed_bexps (tflatten ess) E = all (well_formed_bexps^~E) ess.
    Proof.
      rewrite /well_formed_bexps /=. rewrite all_tflatten. reflexivity.
    Qed.

    Lemma eval_exp_size e te s :
      well_formed_exp e te -> S.conform s te -> size (eval_exp e s) = exp_size e te.
    Proof.
      elim: e te s => //=.
      - move=> v te s Hmem Hcon. by rewrite (S.conform_mem Hcon Hmem).
      - case => /=.
        + move => e IH te s Hwf Hcon. rewrite -(IH _ _ Hwf Hcon) /invB size_map.
          reflexivity.
        + move=> e IH te s Hwf Hcon.
          rewrite /negB /invB size_succB size_map (IH _ _ Hwf Hcon). reflexivity.
        + move=> *. rewrite size_extract. reflexivity.
        + move=> *. rewrite size_high. reflexivity.
        + move=> *. rewrite size_low. reflexivity.
        + move => n e IH te s Hwf Hcon. rewrite size_zext (IH _ _ Hwf Hcon).
          reflexivity.
        + move => n e IH te s Hwf Hcon. rewrite size_sext (IH _ _ Hwf Hcon).
          reflexivity.
        + move => n e IH te s Hwf Hcon. rewrite size_repeat (IH _ _ Hwf Hcon). 
          reflexivity.
        + move => n e IH te s Hwf Hcon. rewrite size_rolB (IH _ _ Hwf Hcon). 
          reflexivity.
        + move => n e IH te s Hwf Hcon. rewrite size_rorB (IH _ _ Hwf Hcon). 
          reflexivity.
      - case => e0 IH0 e1 IH1 te s /andP [/andP [/andP [Hwf0 Hwf1] Hszgt0] Hsize] Hcon /=.
        + rewrite /andB size_lift (IH0 _ _ Hwf0 Hcon) (IH1 _ _ Hwf1 Hcon).
          reflexivity.
        + rewrite /orB size_lift (IH0 _ _ Hwf0 Hcon) (IH1 _ _ Hwf1 Hcon).
          reflexivity.
        + rewrite /xorB size_lift (IH0 _ _ Hwf0 Hcon) (IH1 _ _ Hwf1 Hcon).
          reflexivity.
        + rewrite size_addB (IH0 _ _ Hwf0 Hcon) (IH1 _ _ Hwf1 Hcon). reflexivity.
        + rewrite size_subB (IH0 _ _ Hwf0 Hcon) (IH1 _ _ Hwf1 Hcon). reflexivity.
        + rewrite size_mulB (IH0 _ _ Hwf0 Hcon). reflexivity.
        + rewrite size_udivB (IH0 _ _ Hwf0 Hcon). reflexivity.
        + rewrite size_uremB (IH0 _ _ Hwf0 Hcon). reflexivity.
        + rewrite size_sdivB (IH0 _ _ Hwf0 Hcon). reflexivity.
        + rewrite size_sremB (IH0 _ _ Hwf0 Hcon). reflexivity.
        + rewrite size_smodB_ss.
          * rewrite (IH0 _ _ Hwf0 Hcon). reflexivity.
          * rewrite (IH0 _ _ Hwf0 Hcon) (IH1 _ _ Hwf1 Hcon). exact: (eqP Hsize).
        + rewrite shlBB_shlB size_shlB (IH0 _ _ Hwf0 Hcon). reflexivity.
        + rewrite shrBB_shrB size_shrB (IH0 _ _ Hwf0 Hcon). reflexivity.
        + rewrite sarBB_sarB size_sarB (IH0 _ _ Hwf0 Hcon). reflexivity.
        + rewrite size_cat (IH0 _ _ Hwf0 Hcon) (IH1 _ _ Hwf1 Hcon). rewrite addnC.
          reflexivity.
        + reflexivity.
      - move => c e0 IH0 e1 IH1 te s /andP
                  [/andP [/andP [Hwfc Hwf0] Hwf1] Hsize] Hcon.
        rewrite (eqP Hsize) maxnn. case: (eval_bexp c s).
        + rewrite (IH0 _ _ Hwf0 Hcon). exact: (eqP Hsize).
        + rewrite (IH1 _ _ Hwf1 Hcon). reflexivity.
    Qed.

    Lemma exp_size_submap E1 E2 e :
      TELemmas.submap E1 E2 -> well_formed_exp e E1 ->
      exp_size e E1 = exp_size e E2.
    Proof.
      move=> Hsub. elim: e => //=.
      - move=> v Hmem1. move: (TELemmas.mem_find_some Hmem1) => [ty Hfind1].
        move: (Hsub _ _ Hfind1) => Hfind2.
        move: (TE.find_some_vtyp Hfind1) (TE.find_some_vtyp Hfind2) => Hty1 Hty2.
        rewrite !TE.vtyp_vsize Hty1 Hty2. reflexivity.
      - move=> op e IH Hwf. move: (IH Hwf) => {IH} IH. case: op => //=.
        + move=> n. rewrite IH. reflexivity.
        + move=> n. rewrite IH. reflexivity.
        + move=> n. rewrite IH. reflexivity.
      - move=> op e1 IH1 e2 IH2 /andP [/andP [/andP [Hwf1 Hwf2] Hszgt0] Hs].
        move: (IH1 Hwf1) (IH2 Hwf2) => {IH1 IH2} IH1 IH2. move: Hs.
        case: op => //=; rewrite IH1 IH2; reflexivity.
      - move=> b e1 IH1 e2 IH2 /andP [/andP [/andP [Hwfb Hwf1] Hwf2] Hs].
        rewrite (IH1 Hwf1) (IH2 Hwf2). reflexivity.
    Qed.

    Lemma well_formed_exp_submap E1 E2 e :
      TELemmas.submap E1 E2 -> well_formed_exp e E1 -> well_formed_exp e E2
    with well_formed_bexp_submap E1 E2 e :
           TELemmas.submap E1 E2 -> well_formed_bexp e E1 -> well_formed_bexp e E2.
    Proof.
      (* well_formed_exp_submap *)
      move=> Hsub. elim: e => //=.
      - move=> v Hmem1. exact: (TELemmas.submap_mem Hsub Hmem1).
      - move=> op e1 IH1 e2 IH2 /andP [/andP [/andP [Hwf1 Hwf2] Hszgt0] Hs].
        rewrite (well_formed_exp_submap _ _ _ Hsub Hwf1)
                (well_formed_exp_submap _ _ _ Hsub Hwf2).
        rewrite -(exp_size_submap Hsub Hwf1) -(exp_size_submap Hsub Hwf2).
          by rewrite Hszgt0 Hs.
      - move=> b e1 IH1 e2 IH2 /andP [/andP [/andP [Hwfb Hwf1] Hwf2] Hs].
        rewrite (well_formed_bexp_submap _ _ _ Hsub Hwfb)
                (well_formed_exp_submap _ _ _ Hsub Hwf1)
                (well_formed_exp_submap _ _ _ Hsub Hwf2).
        rewrite -(exp_size_submap Hsub Hwf1) -(exp_size_submap Hsub Hwf2).
          by rewrite Hs.
      (* well_formed_bexp_submap *)
      move=> Hsub. elim: e => //=.
      - move=> op e1 e2 /andP [/andP [Hwf1 Hwf2] Hs].
        rewrite (well_formed_exp_submap _ _ _ Hsub Hwf1)
                (well_formed_exp_submap _ _ _ Hsub Hwf2).
        rewrite -(exp_size_submap Hsub Hwf1) -(exp_size_submap Hsub Hwf2).
          by rewrite Hs.
      - move=> e1 IH1 e2 IH2 /andP [Hwf1 Hwf2].
        by rewrite (well_formed_bexp_submap _ _ _ Hsub Hwf1)
                   (well_formed_bexp_submap _ _ _ Hsub Hwf2).
      - move=> e1 IH1 e2 IH2 /andP [Hwf1 Hwf2].
        by rewrite (well_formed_bexp_submap _ _ _ Hsub Hwf1)
                   (well_formed_bexp_submap _ _ _ Hsub Hwf2).
    Qed.

    Lemma well_formed_bexps_submap E1 E2 es :
      TELemmas.submap E1 E2 -> well_formed_bexps es E1 -> well_formed_bexps es E2.
    Proof.
      elim: es => [| e es IH] //=. move=> Hsub. move/andP => [He Hes].
      by rewrite (well_formed_bexp_submap Hsub He) (IH Hsub Hes).
    Qed.


  End WellFormed.


  (* Split conjunctions *)

  Fixpoint split_conj (e : bexp) : seq bexp :=
    match e with
    | Bconj e1 e2 => split_conj e1 ++ split_conj e2
    | _ => [:: e]
    end.

  Lemma split_conj_eval s e :
    eval_bexp e s <-> (forall f, (f \in split_conj e) -> eval_bexp f s).
  Proof.
    split.
    - elim: e => //=.
      + move=> _ ef Hin. rewrite mem_seq1 in Hin. by rewrite (eqP Hin).
      + move=> op e1 e2 He f Hin. rewrite mem_seq1 in Hin. by rewrite (eqP Hin).
      + move=> e IH He f Hin. rewrite mem_seq1 in Hin. by rewrite (eqP Hin).
      + move=> e1 IH1 e2 IH2 /andP [He1 He2] f Hin. rewrite mem_cat in Hin.
        case/orP: Hin => Hin.
        * exact: (IH1 He1 _  Hin).
        * exact: (IH2 He2 _  Hin).
      + move=> e1 IH1 e2 IH2 He f Hin. rewrite mem_seq1 in Hin. by rewrite (eqP Hin).
    - elim: e => //=.
      + move=> H. move: (H Bfalse). rewrite mem_seq1 eqxx. by apply.
      + move=> op e1 e2 H. move: (H (Bbinop op e1 e2)).
        rewrite mem_seq1 eqxx. by apply.
    + move=> e IH H. move: (H (Blneg e)). rewrite mem_seq1 eqxx. by apply.
    + move=> e1 IH1 e2 IH2 H. apply/andP; split.
      * apply: IH1. move=> f Hin. apply: H. rewrite mem_cat Hin orTb. reflexivity.
      * apply: IH2. move=> f Hin. apply: H. rewrite mem_cat Hin orbT. reflexivity.
    + move=> e1 IH1 e2 IH2 H. move: (H (Bdisj e1 e2)).
       rewrite mem_seq1 eqxx. by apply.
  Qed.


  (**
   * Make conjunctions of QFBV expressions.
   * - [qfbv_conjs] is right associative and is easier for induction
   * - [qfbv_conjs_la] is left associative and is better for bit-blasting
   *   with cache *)

  Section QFBVConjs.

    (** Make conjunctions of QFBV expressions
      (right associativity, easy for induction) *)

    Fixpoint qfbv_conjs es :=
      match es with
      | [::] => Btrue
      | hd::tl => qfbv_conj hd (qfbv_conjs tl)
      end.

    Lemma vars_qfbv_conjs es : vars_bexp (qfbv_conjs es) = vars_bexps es.
    Proof. elim: es => [| e es IH] //=. rewrite IH. reflexivity. Qed.

    Lemma eval_qfbv_conjs_rcons es e s :
      eval_bexp (qfbv_conjs (rcons es e)) s =
        eval_bexp (qfbv_conjs es) s && eval_bexp e s.
    Proof.
      elim: es => [| h es IH] /=.
      - rewrite andbT. reflexivity.
      - rewrite -(@andbA _ _ (eval_bexp e s)). rewrite -IH. reflexivity.
    Qed.

    Lemma eval_qfbv_conjs_cat es1 es2 s :
      eval_bexp (qfbv_conjs (es1 ++ es2)) s =
        eval_bexp (qfbv_conjs es1) s && eval_bexp (qfbv_conjs es2) s.
    Proof.
      elim: es1 es2 => [| e1 es1 IH] es2 //=.
      rewrite -(@andbA _ _ (eval_bexp (qfbv_conjs es2) s)).
      rewrite -IH. reflexivity.
    Qed.

    Lemma eval_qfbv_conjs_rev es s :
      eval_bexp (qfbv_conjs (rev es)) s <-> eval_bexp (qfbv_conjs es) s.
    Proof.
      elim: es => [| e es IH] //=. rewrite rev_cons. rewrite eval_qfbv_conjs_rcons.
      move: IH=> [IH1 IH2]. split; move/andP=> [H1 H2].
      - by rewrite (IH1 H1) H2.
      - by rewrite (IH2 H2) H1.
    Qed.

    Lemma qfbv_conjs_inj es1 es2 :
      qfbv_conjs es1 = qfbv_conjs es2 -> es1 = es2.
    Proof.
      elim: es1 es2 => [| e1 es1 IH] [| e2 es2] //=.
      case=> H1 H2. rewrite H1 (IH _ H2). reflexivity.
    Qed.

    Lemma well_formed_bexp_qfbv_conjs_rcons E es e :
      well_formed_bexp (qfbv_conjs (rcons es e)) E =
        well_formed_bexp (qfbv_conjs es) E && well_formed_bexp e E.
    Proof.
      elim: es => [| hd tl IH] /=.
      - rewrite andbT. reflexivity.
      - rewrite -andbA. rewrite -IH. reflexivity.
    Qed.

    Lemma well_formed_bexp_qfbv_conjs_rev E es :
      well_formed_bexp (qfbv_conjs (rev es)) E = well_formed_bexp (qfbv_conjs es) E.
    Proof.
      elim: es => [| e es IH] //=. rewrite rev_cons.
      rewrite well_formed_bexp_qfbv_conjs_rcons. rewrite IH. rewrite andbC.
      reflexivity.
    Qed.

    Lemma qfbv_conjs_well_formed E es :
      well_formed_bexp (qfbv_conjs es) E = well_formed_bexps es E.
    Proof. elim: es => [| e es IH] //=. rewrite IH. reflexivity. Qed.

    (* Make conjunctions of QFBV expressions
     (left associativity, good for bit-blasting cache) *)

    Fixpoint qfbv_conjs_rec pre_es es :=
      match es with
      | [::] => pre_es
      | hd::tl => qfbv_conjs_rec (qfbv_conj pre_es hd) tl
      end.

    (* Add QFBV.Btrue at the beginning to make qfbv_conjs_la injective *)
    Definition qfbv_conjs_la es :=
      match es with
      | [::] => Btrue
      | e::es => qfbv_conjs_rec (qfbv_conj Btrue e) es
      end.

    Lemma vars_qfbv_conjs_rec pres es :
      VS.Equal (vars_bexp (qfbv_conjs_rec pres es)) (VS.union (vars_bexp pres) (vars_bexps es)).
    Proof.
      elim: es pres => [| e es IH] pres //=.
      - rewrite VSLemmas.union_emptyr. reflexivity.
      - rewrite IH. rewrite /qfbv_conj /=. by VSLemmas.dp_Equal.
    Qed.

    Lemma vars_qfbv_conjs_la es :
      VS.Equal (vars_bexp (qfbv_conjs_la es)) (vars_bexps es).
    Proof.
      rewrite /qfbv_conjs_la. case: es => [| e es] //=. rewrite vars_qfbv_conjs_rec /=.
      rewrite VSLemmas.union_emptyl. reflexivity.
    Qed.

    Lemma qfbv_conjs_rec_singleton pre_es e :
      qfbv_conjs_rec pre_es [::e] = qfbv_conj pre_es e.
    Proof. reflexivity. Qed.

    Lemma qfbv_conjs_rec_cons pre_es e es :
      qfbv_conjs_rec pre_es (e::es) = qfbv_conjs_rec (qfbv_conj pre_es e) es.
    Proof. reflexivity. Qed.

    Lemma qfbv_conjs_rec_cat pre_es es1 es2 :
      qfbv_conjs_rec pre_es (es1 ++ es2) =
        qfbv_conjs_rec (qfbv_conjs_rec pre_es es1) es2.
    Proof. elim: es1 pre_es es2 => [| e1 es1 IH] //=. Qed.

    Lemma qfbv_conjs_rec_rcons pre_es es e :
      qfbv_conjs_rec pre_es (rcons es e) = qfbv_conj (qfbv_conjs_rec pre_es es) e.
    Proof. by elim: es pre_es e => [| hd tl IH] //=. Qed.

    Lemma qfbv_conjs_rec_conj e1 es1 e2 es2 :
      qfbv_conjs_rec (qfbv_conj Btrue e1) es1 =
        qfbv_conjs_rec (qfbv_conj Btrue e2) es2 ->
      e1 = e2 /\ es1 = es2.
    Proof.
      move: es1 es2 e1 e2. apply: last_ind => //=.
      - case=> [| e3 es2] e1 e2 //=.
        + case. by move=> ->.
        + move=> H. apply: False_ind. move: H. move: {2}Btrue.
          elim: es2 e1 e2 e3 => [| e es IH] e1 e2 e3 e4 //= H. apply: IH. exact: H.
      - move=> es1 le1 IH. case/lastP => //=.
        + move=> e1 e2 H. apply: False_ind. move: H. move: {1}Btrue.
          clear IH. elim: es1 le1 e1 e2 => [| e es IH] e1 e2 e3 e4 //= H. apply: IH.
          exact: H.
        + move=> es2 le2 e1 e2 /= H. rewrite !qfbv_conjs_rec_rcons in H.
          case: H. move=> H1 ->. move: (IH _ _ _ H1). case=> -> ->. done.
    Qed.

    Lemma qfbv_conjs_la_inj es1 es2 :
      qfbv_conjs_la es1 = qfbv_conjs_la es2 -> es1 = es2.
    Proof.
      rewrite /qfbv_conjs_la. case: es1 => [| e1 es1] //=.
      - case: es2 => [| e2 es2] //=. move: {2}Btrue. move=> e1 H.
        apply: False_ind. elim: es2 e1 e2 H => [| e es IH] e1 e2 /= H.
        + discriminate.
        + apply: IH. exact: H.
      - case: es2 => [| e2 es2] //=.
        + move: {1}Btrue. move=> e2 H. apply: False_ind.
          elim: es1 e1 e2 H => [| e es IH] e1 e2 /= H.
          * discriminate.
          * apply: IH. exact: H.
        + move=> H. move: (qfbv_conjs_rec_conj H) => [-> ->]. reflexivity.
    Qed.

    Lemma eval_qfbv_conjs_rec s pre_es es :
      eval_bexp (qfbv_conjs_rec pre_es es) s =
        eval_bexp pre_es s && eval_bexp (qfbv_conjs_la es) s.
    Proof.
      rewrite /qfbv_conjs_la. case: es => [| e1 es] //=.
      - rewrite andbT. reflexivity.
      - move: es pre_es e1. apply: last_ind => //=.
        move=> es le1 IH pre_es e1. rewrite !qfbv_conjs_rec_rcons /=.
        rewrite IH. rewrite !andbA. reflexivity.
    Qed.

    Lemma eval_qfbv_conjs_rec_ra s pre_es es :
      eval_bexp (qfbv_conjs_rec pre_es es) s =
        eval_bexp pre_es s && eval_bexp (qfbv_conjs es) s.
    Proof.
      elim: es pre_es => [| e1 es IH] pre_es //=.
      - rewrite andbT. reflexivity.
      - rewrite IH. rewrite /qfbv_conj /=. rewrite andbA. reflexivity.
    Qed.

    Lemma eval_qfbv_conjs_la_rcons es e s :
      eval_bexp (qfbv_conjs_la (rcons es e)) s =
        eval_bexp (qfbv_conjs_la es) s && eval_bexp e s.
    Proof.
      rewrite /qfbv_conjs_la. case: es => [| e1 es] //=.
      rewrite qfbv_conjs_rec_rcons /=. reflexivity.
    Qed.

    Lemma eval_qfbv_conjs_la_cat es1 es2 s :
      eval_bexp (qfbv_conjs_la (es1 ++ es2)) s =
        eval_bexp (qfbv_conjs_la es1) s && eval_bexp (qfbv_conjs_la es2) s.
    Proof.
      rewrite /qfbv_conjs_la. case: es1 => [| e1 es1] //=. case: es2 => [| e2 es2] //=.
      - rewrite cats0 andbT. reflexivity.
      - move: es2 e1 e2 es1. apply: last_ind => //=.
        + move=> e1 e2 es1. rewrite cats1. rewrite qfbv_conjs_rec_rcons /=.
          reflexivity.
        + move=> es2 le2 IH. move=> e1 e2 es1. rewrite qfbv_conjs_rec_rcons /=.
          rewrite -cat_rcons. rewrite -rcons_cat. rewrite qfbv_conjs_rec_rcons /=.
          rewrite cat_rcons. rewrite IH. rewrite !andbA. reflexivity.
    Qed.

    Lemma eval_qfbv_conjs_ra_la s es :
      eval_bexp (qfbv_conjs es) s = eval_bexp (qfbv_conjs_la es) s.
    Proof.
      rewrite /qfbv_conjs_la. case: es => [| e1 es] //=.
      move: es e1. apply: last_ind => //=.
      - move=> e1. rewrite andbT. reflexivity.
      - move=> es le IH e1. rewrite qfbv_conjs_rec_rcons /=. rewrite -IH.
        rewrite eval_qfbv_conjs_rcons. rewrite andbA. reflexivity.
    Qed.

    Lemma eval_qfbv_conjs_la_rev es s :
      eval_bexp (qfbv_conjs_la (rev es)) s <-> eval_bexp (qfbv_conjs_la es) s.
    Proof.
      elim: es => [| e es IH] //=. rewrite rev_cons.
      rewrite eval_qfbv_conjs_la_rcons. rewrite eval_qfbv_conjs_rec /=.
      rewrite andbC. by case: (eval_bexp e s).
    Qed.

    Lemma well_formed_bexp_qfbv_conjs_rec_rcons E pre_es es e :
      well_formed_bexp (qfbv_conjs_rec pre_es (rcons es e)) E =
        well_formed_bexp (qfbv_conjs_rec pre_es es) E && well_formed_bexp e E.
    Proof.
      case: es => [| e1 es] //=. rewrite qfbv_conjs_rec_rcons /=. reflexivity.
    Qed.

    Lemma well_formed_bexp_qfbv_conjs_la_rcons E es e :
      well_formed_bexp (qfbv_conjs_la (rcons es e)) E =
        well_formed_bexp (qfbv_conjs_la es) E && well_formed_bexp e E.
    Proof.
      rewrite /qfbv_conjs_la. case: es => [| e1 es] //=.
      rewrite qfbv_conjs_rec_rcons /=. reflexivity.
    Qed.

    Lemma well_formed_bexp_ra_la E es :
      well_formed_bexp (qfbv_conjs es) E = well_formed_bexp (qfbv_conjs_la es) E.
    Proof.
      rewrite /qfbv_conjs_la. case: es => [| e es] //=.
      move: es e. apply: last_ind => //=.
      - move=> e. rewrite andbT. reflexivity.
      - move=> es le IH e. rewrite well_formed_bexp_qfbv_conjs_rec_rcons.
        rewrite -IH. rewrite well_formed_bexp_qfbv_conjs_rcons. rewrite andbA.
        reflexivity.
    Qed.

    Lemma well_formed_bexp_qfbv_conjs_la_rev E es :
      well_formed_bexp (qfbv_conjs_la (rev es)) E =
        well_formed_bexp (qfbv_conjs_la es) E.
    Proof.
      rewrite -!well_formed_bexp_ra_la. exact: well_formed_bexp_qfbv_conjs_rev.
    Qed.

    Lemma qfbv_conjs_la_well_formed E es :
      well_formed_bexp (qfbv_conjs_la es) E = well_formed_bexps es E.
    Proof. rewrite -well_formed_bexp_ra_la. exact: qfbv_conjs_well_formed. Qed.

  End QFBVConjs.


  (* Evaluation of a sequence of QF_BV predicates *)

  Definition eval_bexps (es : seq bexp) (s : state) : bool :=
    all (eval_bexp^~ s) es.

  Lemma eval_bexps_cons e es s : eval_bexps (e::es) s = (eval_bexp e s && eval_bexps es s).
  Proof. rewrite /eval_bexps /=. reflexivity. Qed.

  Lemma eval_bexps_rcons es e s : eval_bexps (rcons es e) s = (eval_bexps es s && eval_bexp e s).
  Proof. rewrite /eval_bexps all_rcons. rewrite andbC. reflexivity. Qed.

  Lemma eval_bexps_cat es1 es2 s : eval_bexps (es1 ++ es2) s = (eval_bexps es1 s && eval_bexps es2 s).
  Proof. rewrite /eval_bexps all_cat. reflexivity. Qed.

  Lemma eval_bexps_rev es s : eval_bexps (rev es) s = eval_bexps es s.
  Proof.
    elim: es => [| e es IH] //=. rewrite rev_cons. rewrite eval_bexps_rcons IH.
    by rewrite andbC.
  Qed.

  Lemma eval_bexps_tflatten ess s :
    eval_bexps (tflatten ess) s = all (eval_bexps^~ s) ess.
  Proof.
    elim: ess => [| es ess IH] //=. rewrite tflatten_cons. rewrite eval_bexps_cat.
    rewrite IH. rewrite andbC. rewrite eval_bexps_rev. reflexivity.
  Qed.

  Lemma qfbv_conjs_eval es s : eval_bexp (qfbv_conjs es) s = eval_bexps es s.
  Proof. elim: es => [| e es IH] //=. by rewrite IH. Qed.

  Lemma qfbv_conj_la_eval es s : eval_bexp (qfbv_conjs_la es) s = eval_bexps es s.
  Proof. rewrite -eval_qfbv_conjs_ra_la. exact: qfbv_conjs_eval. Qed.


  (* Proper *)

  Lemma eval_exp_equal e s1 s2 :
    S.Equal s1 s2 -> eval_exp e s1 = eval_exp e s2
  with eval_bexp_equal e s1 s2 :
    S.Equal s1 s2 -> eval_bexp e s1 = eval_bexp e s2.
  Proof.
    (* eval_exp_equal *)
    - move=> Heq. case: e => //=.
      + move=> x. by rewrite -> Heq.
      + move=> op e. by rewrite (eval_exp_equal _ _ _ Heq).
      + move=> op e1 e2. by rewrite !(eval_exp_equal _ _ _ Heq).
      + move=> b e1 e2. by rewrite (eval_bexp_equal _ _ _ Heq) !(eval_exp_equal _ _ _ Heq).
    (* eval_bexp_equal *)
    - move=> Heq. case: e => //=.
      + move=> op e1 e2. by rewrite !(eval_exp_equal _ _ _ Heq).
      + move=> e. by rewrite (eval_bexp_equal _ _ _ Heq).
      + move=> e1 e2. by rewrite !(eval_bexp_equal _ _ _ Heq).
      + move=> e1 e2. by rewrite !(eval_bexp_equal _ _ _ Heq).
  Qed.

  Global Instance add_proper_eval_exp : Proper (eq ==> S.Equal ==> eq) eval_exp.
  Proof.
    move=> e1 e2 ? s1 s2 Heq; subst. exact: (eval_exp_equal _ Heq).
  Qed.

  Global Instance add_proper_eval_bexp : Proper (eq ==> S.Equal ==> eq) eval_bexp.
  Proof.
    move=> e1 e2 ? s1 s2 Heq; subst. exact: (eval_bexp_equal _ Heq).
  Qed.

  Global Instance add_proper_eval_bexps : Proper (eq ==> S.Equal ==> eq) eval_bexps.
  Proof.
    move=> es1 es2 ? s1 s2 Heq; subst. elim: es2 => [| e es IH] //=.
    rewrite -> Heq at 1. by rewrite IH.
  Qed.

  Global Instance add_proper_exp_size : Proper (eq ==> TE.Equal ==> eq) exp_size.
  Proof.
    move=> e1 e2 ? E1 E2 Heq; subst. elim: e2 => //=.
    - move=> v. rewrite Heq. reflexivity.
    - move=> op e IH. rewrite IH. reflexivity.
    - move=> op e1 IH1 e2 IH2. rewrite IH1 IH2. reflexivity.
    - move=> _ e1 IH1 e2 IH2. rewrite IH1 IH2. reflexivity.
  Qed.

  Lemma well_formed_exp_env_equal E1 E2 e :
    TE.Equal E1 E2 -> well_formed_exp e E1 = well_formed_exp e E2
  with well_formed_bexp_env_equal E1 E2 e :
    TE.Equal E1 E2 -> well_formed_bexp e E1 = well_formed_bexp e E2.
  Proof.
    - (* well_formed_exp_env_equal *)
      case: e => //=.
      + move=> v ->. reflexivity.
      + move=> _ e Heq. rewrite (well_formed_exp_env_equal _ _ _ Heq). reflexivity.
      + move=> op e1 e2 Heq. rewrite 2!(well_formed_exp_env_equal _ _ _ Heq).
        rewrite Heq. reflexivity.
      + move=> b e1 e2 Heq. rewrite (well_formed_bexp_env_equal _ _ _ Heq)
                                    2!(well_formed_exp_env_equal _ _ _ Heq).
        rewrite Heq. reflexivity.
    - (* well_formed_bexp_env_equal *)
      case: e => //=.
      + move=> _ e1 e2 Heq. rewrite 2!(well_formed_exp_env_equal _ _ _ Heq).
        rewrite Heq. reflexivity.
      + move=> b Heq. rewrite (well_formed_bexp_env_equal _ _ _ Heq). reflexivity.
      + move=> b1 b2 Heq. rewrite 2!(well_formed_bexp_env_equal _ _ _ Heq). reflexivity.
      + move=> b1 b2 Heq. rewrite 2!(well_formed_bexp_env_equal _ _ _ Heq). reflexivity.
  Qed.

  Global Instance add_proper_well_formed_exp : Proper (eq ==> TE.Equal ==> eq) well_formed_exp.
  Proof. move=> e1 e2 ? E1 E2 Heq; subst. exact: well_formed_exp_env_equal. Qed.

  Global Instance add_proper_well_formed_bexp : Proper (eq ==> TE.Equal ==> eq) well_formed_bexp.
  Proof. move=> e1 e2 ? E1 E2 Heq; subst. exact: well_formed_bexp_env_equal. Qed.

  Global Instance add_proper_well_formed_bexps : Proper (eq ==> TE.Equal ==> eq) well_formed_bexps.
  Proof.
    move=> es1 es2 ? E1 E2 Heq; subst. elim: es2 => [| e es IH] //=.
    rewrite IH Heq. reflexivity.
  Qed.


  (* Check validity of a sequence of QFBV formulas *)

  Definition valid_bexps E (es : seq bexp) :=
    forall s, S.conform s E -> eval_bexps es s.

  Lemma valid_bexps_cons E e es :
    valid_bexps E (e::es) <-> valid E e /\ valid_bexps E es.
  Proof.
    split.
    - move=> H. split.
      + move=> s Hco. move: (H _ Hco). rewrite eval_bexps_cons. move/andP. tauto.
      + move=> s Hco. move: (H _ Hco). rewrite eval_bexps_cons. move/andP. tauto.
    - move=> [He Hes] s Hco. rewrite eval_bexps_cons. apply/andP.
      move: (He _ Hco) (Hes _ Hco). tauto.
  Qed.

  Lemma valid_bexps_rcons E es e :
    valid_bexps E (rcons es e) <-> valid_bexps E es /\ valid E e.
  Proof.
    split.
    - move=> H; split.
      + move=> s Hco. move: (H _ Hco). rewrite eval_bexps_rcons. move/andP. tauto.
      + move=> s Hco. move: (H _ Hco). rewrite eval_bexps_rcons. move/andP. tauto.
    - move=> [Hes He] s Hco. rewrite eval_bexps_rcons.
      apply/andP. move: (He _ Hco) (Hes _ Hco). tauto.
  Qed.

  Lemma valid_bexps_rev E es :
    valid_bexps E (rev es) <-> valid_bexps E es.
  Proof.
    elim: es => [| e es [IH1 IH2]] //=. rewrite rev_cons valid_bexps_rcons.
    rewrite valid_bexps_cons. tauto.
  Qed.

  Lemma valid_bexps_cat E es1 es2 :
    valid_bexps E (es1 ++ es2) <-> valid_bexps E es1 /\ valid_bexps E es2.
  Proof.
    split.
    - move=> H; split.
      + move=> s Hco. move: (H _ Hco). rewrite eval_bexps_cat. move/andP. tauto.
      + move=> s Hco. move: (H _ Hco). rewrite eval_bexps_cat. move/andP. tauto.
    - move=> [H1 H2] s Hco. rewrite eval_bexps_cat.
      apply/andP. move: (H1 _ Hco) (H2 _ Hco). tauto.
  Qed.

  Lemma valid_bexps_all E es :
    valid_bexps E es <-> forall e, e \in es -> valid_bexp E e.
  Proof.
    elim: es => [| e es IH] //=. move: IH => [IH1 IH2]. split=> H.
    - move/valid_bexps_cons: H => [He Hes]. move=> f. rewrite in_cons.
      case/orP=> Hin.
      + move/eqP: Hin => ?; subst. assumption.
      + exact: (IH1 Hes _ Hin).
    - apply/valid_bexps_cons. split.
      + apply: H. exact: mem_head.
      + apply: IH2. move=> f Hin. apply: H. by rewrite in_cons Hin orbT.
  Qed.

  Lemma valid_bexps_flatten E ess :
    valid_bexps E (flatten ess) <-> forall es, es \in ess -> valid_bexps E es.
  Proof.
    elim: ess => [| es ess IH] //=. move: IH => [IH1 IH2]. split => H.
    - move/valid_bexps_cat: H => [Hes Hess]. move=> fs. rewrite in_cons.
      case/orP => Hin.
      + move/eqP: Hin => ?; subst. assumption.
      + exact: (IH1 Hess _ Hin).
    - apply/valid_bexps_cat. split.
      + apply: H. exact: mem_head.
      + apply: IH2. move=> fs Hin. apply: H. by rewrite in_cons Hin orbT.
  Qed.

  Lemma valid_bexps_tflatten E ess :
    valid_bexps E (tflatten ess) <-> forall es, es \in ess -> valid_bexps E es.
  Proof.
    rewrite tflatten_flatten. split => H.
    - apply/valid_bexps_flatten. apply/valid_bexps_rev. assumption.
    - apply/valid_bexps_rev. apply/valid_bexps_flatten. assumption.
  Qed.


  (* Simplification *)

  Fixpoint simplify_bexp (e : bexp) : bexp :=
    match e with
    | Btrue | Bfalse | Bbinop _ _ _ => e
    | Blneg e => match simplify_bexp e with
                 | Btrue => Bfalse
                 | Bfalse => Btrue
                 | Blneg e => e
                 | e => Blneg e
                 end
    | Bconj e1 e2 => match simplify_bexp e1, simplify_bexp e2 with
                        | Btrue, e2 => e2
                        | Bfalse, _ => Bfalse
                        | e1, Btrue => e1
                        | _, Bfalse => Bfalse
                        | e1, e2 => Bconj e1 e2
                        end
    | Bdisj e1 e2 => match simplify_bexp e1, simplify_bexp e2 with
                        | Btrue, _ => Btrue
                        | Bfalse, e2 => e2
                        | _, Btrue => Btrue
                        | e1, Bfalse => e1
                        | e1, e2 => Bdisj e1 e2
                        end
    end.

  Ltac mytac :=
    match goal with
    | H : _ <-> _ |- _ =>
      let H1 := fresh in
      let H2 := fresh in
      (case: H => H1 H2); mytac
    | |- _ <-> _ =>
      let H := fresh in
      split; move=> H; mytac
    | H : is_true (_ && _) |- _ =>
      let H1 := fresh in
      let H2 := fresh in
      (move/andP: H => [H1 H2]); mytac
    | |- is_true (_ && _) =>
      apply/andP; split; mytac
    | H : is_true (_ || _) |- _ =>
      (case/orP: H => H); mytac
    | |- is_true (_ || _) =>
      apply/orP; mytac
    | H : is_true true -> ?e |- _ =>
      (move: (H is_true_true) => {} H); mytac
    | H1 : ?e1 -> _, H2 : ?e1 |- _ => (move: (H1 H2) => {} H1); mytac
    | |- is_true (~~ _) => let H := fresh in apply/negP=> H; mytac
    | H1 : is_true ?e,
      H2 : is_true (~~ ?e)
      |- _ => rewrite H1 in H2; discriminate
    | H1 : is_true (~~ ?b) -> is_true ?e,
      H2 : is_true (~~ ?e)
      |- is_true ?b =>
      let Hbs := fresh in
      let He := fresh in
      (dcase b); (case=> Hbs); [
        reflexivity
      | (move/idP/negP: Hbs => Hbs); (move: (H1 Hbs) => He); rewrite He in H2;
        discriminate ]
    | H1 : is_true (?e1 && ?e2) -> _,
      H2 : is_true ?e1, H3 : is_true ?e2 |- _ =>
      (rewrite H2 H3 /= in H1); (move: (H1 is_true_true) => {} H1); mytac
    | H1 : is_true (?e1 || ?e2) -> _,
      H2 : is_true ?e1 |- _ =>
      (rewrite H2 orTb in H1); (move: (H1 is_true_true) => {} H1); mytac
    | H1 : is_true (?e1 || ?e2) -> _,
      H2 : is_true ?e2 |- _ =>
      (rewrite H2 orbT in H1); (move: (H1 is_true_true) => {} H1); mytac
    | H1 : is_true (~~ (?e1 && ?e2)),
      H2 : is_true ?e1, H3 : is_true ?e2 |- _ =>
      rewrite H2 H3 /= in H1; discriminate
    | H1 : is_true (~~ (?e1 || ?e2)),
      H2 : is_true ?e1 |- _ =>
      rewrite H2 orTb in H1; discriminate
    | H1 : is_true (~~ (?e1 || ?e2)),
      H2 : is_true ?e2 |- _ =>
      rewrite H2 orbT in H1; discriminate
    | H1 : is_true ?e |- context f [?e] => rewrite H1 /=; mytac
    | |- context f [_ || true] => rewrite orbT; mytac
    | |- is_true true \/ _ => left; reflexivity
    | |- _ \/ is_true true => right; reflexivity
    | H1 : ?e -> is_true false,
      H2 : ?e |- _ => move: (H1 H2); discriminate
    | H : is_true false |- _ => discriminate
    | |- is_true true => reflexivity
    | H : ?e |- ?e => assumption
    | |- _ => idtac
    end.

  Lemma simplify_bexp_eqsat s e :
    eval_bexp (simplify_bexp e) s <-> eval_bexp e s.
  Proof.
    elim: e => //=.
    - move=> e. case: (simplify_bexp e) => /=; intros; by mytac.
    - move=> e1 IH1 e2 IH2. move: IH1 IH2.
      (case: (simplify_bexp e1)); (case: (simplify_bexp e2)); (move => /=);
        intros; by mytac.
    - move=> e1 IH1 e2 IH2. move: IH1 IH2.
      (case: (simplify_bexp e1)); (case: (simplify_bexp e2)); (move => /=);
        intros; by mytac.
  Qed.

  Corollary simplify_bexp_eqvalid E e :
    valid E (simplify_bexp e) <-> valid E e.
  Proof.
    split=> He s Hco.
    - apply/simplify_bexp_eqsat. exact: (He s Hco).
    - apply/simplify_bexp_eqsat. exact: (He s Hco).
  Qed.

  Ltac mytac ::=
    match goal with
    | H : true = ?e |- context f [?e] => rewrite -H /=; mytac
    | H : is_true ?e |- context f [?e] => rewrite H /=; mytac
    | H : is_true (_ && _) |- _ =>
      let H1 := fresh in
      let H2 := fresh in
      move/andP: H => [H1 H2]; mytac
    | H1 : ?e -> _, H2 : ?e |- _ =>
      move: (H1 H2); clear H1; move=> H1; mytac
    | |- true = true => reflexivity
    | |- is_true true => reflexivity
    | |- _ => idtac
    end.

  Lemma simplify_bexp_well_formed E e :
    well_formed_bexp e E -> well_formed_bexp (simplify_bexp e) E.
  Proof.
    elim: e => //=.
    - move=> e. by case Hsb: (simplify_bexp e) => //=.
    - move=> e1 IH1 e2 IH2. move: IH1 IH2.
      (case Hse1: (simplify_bexp e1)); (case Hse2: (simplify_bexp e2));
        (move => //=); intros; by mytac.
    - move=> e1 IH1 e2 IH2. move: IH1 IH2.
      (case Hse1: (simplify_bexp e1)); (case Hse2: (simplify_bexp e2));
        (move => //=); intros; by mytac.
  Qed.


  (* Simplification with trivial implication detection *)

  Definition bexp_is_implied (e : bexp) : bool :=
    match e with
    | Bdisj (Blneg e1) e2 => e2 \in (split_conj e1)
    | _ => false
    end.

  Lemma bexp_is_implied_sat e s :
    bexp_is_implied e -> eval_bexp e s.
  Proof.
    case: e => //=. move=> [] => //=. move=> e1 e2. elim: e1 => //=.
    - rewrite mem_seq1. move/eqP=> ->. reflexivity.
    - move=> op f1 f2. rewrite mem_seq1. move/eqP=> -> /=. exact: orNb.
    - move=> f IH. rewrite mem_seq1. move/eqP=> -> /=. exact: orNb.
    - move=> f1 IH1 f2 IH2. rewrite mem_cat negb_and. case/orP=> Hmem.
      + rewrite (orbC (~~ eval_bexp f1 s)). rewrite -orbA. rewrite (IH1 Hmem) orbT. reflexivity.
      + rewrite -orbA. rewrite (IH2 Hmem) orbT. reflexivity.
    - move=> f1 IH1 f2 IH2. rewrite mem_seq1. move/eqP=> -> /=. exact: orNb.
  Qed.

  Fixpoint simplify_exp (e : exp) : exp :=
    match e with
    | Evar _ | Econst _ => e
    | Eunop op e => let e := simplify_exp e in
                    match e with
                    | Econst bs => Econst ((eunop_denote op) bs)
                    | _ => Eunop op e
                    end
    | Ebinop op e1 e2 => let e1 := simplify_exp e1 in
                         let e2 := simplify_exp e2 in
                         match e1, e2 with
                         | Econst bs1, Econst bs2 => Econst ((ebinop_denote op) bs1 bs2)
                         | _, _ => Ebinop op e1 e2
                         end
    | Eite b e1 e2 => let b := simplify_bexp2 b in
                      let e1 := simplify_exp e1 in
                      let e2 := simplify_exp e2 in
                      match b with
                      | Btrue => e1
                      | Bfalse => e2
                      | _ => Eite b e1 e2
                      end
    end
  with
  simplify_bexp2 (e : bexp) : bexp :=
    match e with
    | Btrue | Bfalse => e
    | Bbinop op e1 e2 => let e1 := simplify_exp e1 in
                         let e2 := simplify_exp e2 in
                         match e1, e2 with
                         | Econst bs1, Econst bs2 => if (bbinop_denote op) bs1 bs2
                                                     then Btrue else Bfalse
                         | _, _ => Bbinop op e1 e2
                         end
    | Blneg e => match simplify_bexp2 e with
                 | Btrue => Bfalse
                 | Bfalse => Btrue
                 | Blneg e => e
                 | e => Blneg e
                 end
    | Bconj e1 e2 => match simplify_bexp2 e1, simplify_bexp2 e2 with
                        | Btrue, e2 => e2
                        | Bfalse, _ => Bfalse
                        | e1, Btrue => e1
                        | _, Bfalse => Bfalse
                        | e1, e2 => Bconj e1 e2
                        end
    | Bdisj e1 e2 => match simplify_bexp2 e1, simplify_bexp2 e2 with
                        | Btrue, _ => Btrue
                        | Bfalse, e2 => e2
                        | _, Btrue => Btrue
                        | e1, Bfalse => e1
                        | e1, e2 => if bexp_is_implied (Bdisj e1 e2) then Btrue
                                    else Bdisj e1 e2
                        end
    end.

  Lemma vars_simplify_exp e :
    VS.subset (vars_exp (simplify_exp e)) (vars_exp e)
  with vars_simplify_bexp2 e :
    VS.subset (vars_bexp (simplify_bexp2 e)) (vars_bexp e).
  Proof.
    - (* simplify_exp_vars *)
      case: e.
      + move=> v /=. exact: VSLemmas.subset_refl.
      + move=> _ /=. exact: VSLemmas.subset_refl.
      + move=> op e /=. move: (vars_simplify_exp e).
        dcase (simplify_exp e). case; simpl; intros; assumption.
      + move=> op e1 e2 /=. move: (vars_simplify_exp e1) (vars_simplify_exp e2).
        dcase (simplify_exp e1). case; simpl; intros.
        * by VSLemmas.dp_subset.
        * move: vars_simplify_exp1. dcase (simplify_exp e2).
          case; simpl; intros; by VSLemmas.dp_subset.
        * by VSLemmas.dp_subset.
        * by VSLemmas.dp_subset.
        * by VSLemmas.dp_subset.
      + move=> b e1 e2 /=. move: (vars_simplify_bexp2 b) (vars_simplify_exp e1) (vars_simplify_exp e2).
        dcase (simplify_bexp2 b). case; simpl; intros; by VSLemmas.dp_subset.
    - (* simplify_bexp_vars *)
      case: e.
      + exact: VSLemmas.subset_refl.
      + exact: VSLemmas.subset_refl.
      + move=> op e1 e2 /=. move: (vars_simplify_exp e1) (vars_simplify_exp e2).
        dcase (simplify_exp e1). case; simpl; intros.
        * by VSLemmas.dp_subset.
        * move: vars_simplify_exp1. dcase (simplify_exp e2).
          case; simpl; intros; case_if; by VSLemmas.dp_subset.
        * by VSLemmas.dp_subset.
        * by VSLemmas.dp_subset.
        * by VSLemmas.dp_subset.
      + move=> e /=. move: (vars_simplify_bexp2 e).
        dcase (simplify_bexp2 e). case; simpl; intros; by VSLemmas.dp_subset.
      + move=> e1 e2 /=. move: (vars_simplify_bexp2 e1) (vars_simplify_bexp2 e2).
        dcase (simplify_bexp2 e1). case; simpl; intros.
        * by VSLemmas.dp_subset.
        * by VSLemmas.dp_subset.
        * move: vars_simplify_bexp1. dcase (simplify_bexp2 e2).
          case; simpl; intros; by VSLemmas.dp_subset.
        * move: vars_simplify_bexp1. dcase (simplify_bexp2 e2).
          case; simpl; intros; by VSLemmas.dp_subset.
        * move: vars_simplify_bexp1. dcase (simplify_bexp2 e2).
          case; simpl; intros; by VSLemmas.dp_subset.
        * move: vars_simplify_bexp1. dcase (simplify_bexp2 e2).
          case; simpl; intros; by VSLemmas.dp_subset.
      + move=> e1 e2 /=. move: (vars_simplify_bexp2 e1) (vars_simplify_bexp2 e2).
        dcase (simplify_bexp2 e1). case; simpl; intros.
        * by VSLemmas.dp_subset.
        * by VSLemmas.dp_subset.
        * move: vars_simplify_bexp1. dcase (simplify_bexp2 e2).
          case; simpl; intros; by VSLemmas.dp_subset.
        * move: vars_simplify_bexp1. dcase (simplify_bexp2 e2).
          case; simpl; intros; case_if; simpl; by VSLemmas.dp_subset.
        * move: vars_simplify_bexp1. dcase (simplify_bexp2 e2).
          case; simpl; intros; by VSLemmas.dp_subset.
        * move: vars_simplify_bexp1. dcase (simplify_bexp2 e2).
          case; simpl; intros; by VSLemmas.dp_subset.
  Qed.

  Lemma simplify_exp_eval s e :
    eval_exp (simplify_exp e) s = eval_exp e s
  with
  simplify_bexp2_eval s e :
    eval_bexp (simplify_bexp2 e) s = eval_bexp e s.
  Proof.
    (* simplify_exp_eval *)
    - elim: e => //=.
      + move=> op e. by case Hs: (simplify_exp e) => /= ->.
      + move=> op e1 IH1 e2 IH2. rewrite -IH1 -IH2 => {IH1 IH2}.
        by case Hs1: (simplify_exp e1); case Hs2: (simplify_exp e2).
      + move=> b e1 IH1 e2 IH2. rewrite -IH1 -IH2 => {IH1 IH2}.
        (case Hs: (simplify_bexp2 b) => //=);
          by rewrite -(simplify_bexp2_eval s b) Hs.
    (* simplify_bexp_eval *)
    - elim: e => //=.
      + move=> op e1 e2. case Hs1: (simplify_exp e1); case Hs2: (simplify_exp e2);
          intros; repeat match goal with
                    | H : simplify_exp ?e = _ |- context c [eval_exp ?e _] =>
                        rewrite -(simplify_exp_eval _ e) H /=
                    end; (done || by case_if).
      + move=> e IH. rewrite -IH => {IH}. case Hs: (simplify_bexp2 e) => //=.
        by rewrite Bool.negb_involutive.
      + move=> e1 IH1 e2 IH2. rewrite -IH1 -IH2 => {IH1 IH2}.
        case: (simplify_bexp2 e1); (case: (simplify_bexp2 e2) => //=);
          intros; repeat match goal with
                    | |- context c [_ && true] => rewrite andbT
                    | |- context c [_ && false] => rewrite andbF
                    end; done.
      + move=> e1 IH1 e2 IH2. rewrite -IH1 -IH2 => {IH1 IH2}.
        case: (simplify_bexp2 e1); (case: (simplify_bexp2 e2) => //=);
          intros; case_if;
          repeat match goal with
            | |- context c [_ || true] => rewrite orbT
            | |- context c [_ || false] => rewrite orbF
            end; try done.
        all: match goal with
             | H : (?e1 \in split_conj ?e2) = true |- context c [eval_bexp ?e2 ?s] =>
                 (move: (@bexp_is_implied_sat (Bdisj (Blneg e2) e1) s H) => /=);
                   by move=> ->
             end.
  Qed.

  Corollary simplify_bexp2_eqsat s e :
    eval_bexp (simplify_bexp2 e) s <-> eval_bexp e s.
  Proof. by rewrite simplify_bexp2_eval. Qed.

  Corollary simplify_bexp2_eqvalid E e :
    valid E (simplify_bexp2 e) <-> valid E e.
  Proof.
    split=> He s Hco.
    - apply/simplify_bexp2_eqsat. exact: (He s Hco).
    - apply/simplify_bexp2_eqsat. exact: (He s Hco).
  Qed.

  Ltac rewrite_to_right :=
    repeat match goal with
      | H : is_true ?e |- context c [?e] => rewrite H /=
      | H : ?e = _ |- context c [?e] => rewrite H /=
      end.

  Ltac rewrite_to_left :=
    repeat match goal with
      | H : is_true ?e |- context c [?e] => rewrite H /=
      | H : _ = ?e |- context c [?e] => rewrite -H /=
      end.

  Lemma simplify_exp_well_formed E e :
    well_formed_exp e E -> well_formed_exp (simplify_exp e) E
  with simplify_bexp2_well_formed E e :
    well_formed_bexp e E -> well_formed_bexp (simplify_bexp2 e) E
  with simplify_exp_size E e :
    well_formed_exp e E ->
    exp_size (simplify_exp e) E = exp_size e E.
  Proof.
    (* simplify_exp_well_formed *)
    - elim: e => //=.
      + move=> op e IH Hwf. move: (IH Hwf) => {IH Hwf}.
        by case: (simplify_exp e).
      + move=> op e1 IH1 e2 IH2 /andP [/andP [/andP [H1 H2] H3] H4].
        move: (IH1 H1) (IH2 H2) => {IH1 IH2}.
        move: (simplify_exp_size E e1 H1) (simplify_exp_size E e2 H2) => {H1 H2}.
        case Hs1: (simplify_exp e1); (case Hs2: (simplify_exp e2) => //=); intros;
          rewrite_to_right; done.
      + move=> b e1 IH1 e2 IH2 /andP [/andP [/andP [Hb H1] H2] Hsize].
        move: (simplify_bexp2_well_formed E b Hb) (IH1 H1) (IH2 H2) => {IH1 IH2 Hb}.
        move: (simplify_exp_size E e1 H1) (simplify_exp_size E e2 H2) => {H1 H2}.
        case Hsb: (simplify_bexp2 b); case Hs1: (simplify_exp e1);
          (case Hs2: (simplify_exp e2) => //=); intros;
          rewrite_to_right; done.
    (* simplify_bexp_well_formed *)
    - elim: e => //=.
      + move=> op e1 e2 /andP [/andP [H1 H2] Hsize].
        move: (simplify_exp_well_formed _ _ H1) (simplify_exp_well_formed _ _ H2).
        move: (simplify_exp_size E e1 H1) (simplify_exp_size E e2 H2) => {H1 H2}.
        case Hs1: (simplify_exp e1); (case Hs2: (simplify_exp e2) => //=); intros;
          rewrite_to_right; done || by case_if.
      + move=> e IH H. move: (IH H) => {IH H}.
        by case: (simplify_bexp2 e).
      + move=> e1 IH1 e2 IH2 /andP [H1 H2]. move: (IH1 H1) (IH2 H2) => {IH1 IH2 H1 H2}.
        case Hs1: (simplify_bexp2 e1); (case Hs2: (simplify_bexp2 e2) => //=);
          by move=> -> ->.
      + move=> e1 IH1 e2 IH2 /andP [H1 H2]. move: (IH1 H1) (IH2 H2) => {IH1 IH2 H1 H2}.
        case Hs1: (simplify_bexp2 e1); (case Hs2: (simplify_bexp2 e2) => //=);
          case_if; simpl; intros; rewrite_to_right; done.
    (* simplify_exp_size *)
    - elim: e => //=.
      + move=> op e IH H. move: (IH H) => {IH H}.
        case Hs: (simplify_exp e) => //=; intros; rewrite_to_left; try done.
        case: op => //=.
        * by rewrite size_invB.
        * by rewrite size_negB.
        * move=> *; by rewrite size_extract.
        * move=> *; by rewrite size_high.
        * move=> *; by rewrite size_low.
        * move=> *; by rewrite size_zext.
        * move=> *; by rewrite size_sext.
        * move=> *; by rewrite size_repeat.
        * move=> *; by rewrite size_rolB.
        * move=> *; by rewrite size_rorB.
      + move=> op e1 IH1 e2 IH2 /andP [/andP [/andP [H1 H2] Hsize1] Hsize2].
        move: (IH1 H1) (IH2 H2) => {IH1 IH2 H1 H2}.
        case Hs1: (simplify_exp e1); case Hs2: (simplify_exp e2); simpl; intros;
          rewrite_to_left; try reflexivity.
        case: op Hsize2 => Hsize2 //=.
        * by rewrite size_andB.
        * by rewrite size_orB.
        * by rewrite size_xorB.
        * by rewrite size_addB.
        * by rewrite size_subB.
        * by rewrite size_mulB.
        * by rewrite size_udivB.
        * by rewrite size_uremB.
        * by rewrite size_sdivB.
        * by rewrite size_sremB.
        * rewrite size_smodB. rewrite size_sremB. case_if => //=.
          rewrite IH1 IH2. rewrite (eqP Hsize2). rewrite minnn. reflexivity.
        * by rewrite shlBB_shlB size_shlB.
        * by rewrite shrBB_shrB size_shrB.
        * by rewrite sarBB_sarB size_sarB.
        * by rewrite size_cat addnC.
      + move=> b e1 IH1 e2 IH2 /andP [/andP [/andP [Hb H1] H2] Hsize].
        (case Hs: (simplify_bexp2 b) => //=);
        rewrite ?(IH1 H1) ?(IH2 H2) !(eqP Hsize); reflexivity || by rewrite maxnn.
  Qed.


  (** String outputs *)

  Definition string_of_eunop (op : eunop) : string :=
    match op with
    | Unot => "bvnot"
    | Uneg => "bvneg"
    | Uextr i j => "(_ extract " ++ string_of_nat i ++ " " ++ string_of_nat j ++ ")"
    | Uhigh n => "(_ high " ++ string_of_nat n ++ ")"
    | Ulow n => "(_ low " ++ string_of_nat n ++ ")"
    | Uzext n => "(_ zero_extend " ++ string_of_nat n ++ ")"
    | Usext n => "(_ sign_extend " ++ string_of_nat n ++ ")"
    | Urepeat n => "(_ repeat " ++ string_of_nat n ++ ")"
    | Urotl n => "(_ rotate_left " ++ string_of_nat n ++ ")"
    | Urotr n => "(_ rotate_right " ++ string_of_nat n ++ ")"
    end.

  Definition string_of_ebinop (op : ebinop) : string :=
    match op with
    | Band => "bvand"
    | Bor => "bvor"
    | Bxor => "bvxor"
    | Badd => "bvadd"
    | Bsub => "bvsub"
    | Bmul => "bvmul"
    | Bdiv => "bvdiv"
    | Bmod => "bvurem"
    | Bsdiv => "bvsdiv"
    | Bsrem => "bvsrem"
    | Bsmod => "bvsmod"
    | Bshl => "bvshl"
    | Blshr => "bvlshr"
    | Bashr => "bvashr"
    | Bconcat => "concat"
    | Bcomp => "bvcomp"
    end.

  Definition string_of_bbinop (op : bbinop) : string :=
    match op with
    | Beq => "="
    | Bult => "bvult"
    | Bule => "bvule"
    | Bugt => "bvugt"
    | Buge => "bvuge"
    | Bslt => "bvslt"
    | Bsle => "bvsle"
    | Bsgt => "bvsgt"
    | Bsge => "bvsge"
    | Buaddo => "bvuaddo"
    | Busubo => "bvusubo"
    | Bumulo => "bvumulo"
    | Bsaddo => "bvsaddo"
    | Bssubo => "bvssubo"
    | Bsmulo => "bvsmulo"
    end.

  Fixpoint string_of_exp (e : exp) : string :=
    match e with
    | Evar v => VP.to_string v
    | Econst bs => "0x" ++ to_hex bs
    | Eunop op e => "(" ++ string_of_eunop op ++ " " ++ string_of_exp e ++ ")"
    | Ebinop op e1 e2 => "(" ++ string_of_ebinop op ++ " " ++
                           string_of_exp e1 ++ " " ++ string_of_exp e2 ++ ")"
    | Eite b e1 e2 => "(ite " ++ string_of_bexp b ++ " " ++
                        string_of_exp e1 ++ " " ++ string_of_exp e2 ++ ")"
    end
  with
  string_of_bexp (e : bexp) : string :=
    match e with
    | Bfalse => "false"
    | Btrue => "true"
    | Bbinop op e1 e2 => "(" ++ string_of_bbinop op ++ " " ++
                           string_of_exp e1 ++ " " ++ string_of_exp e2 ++ ")"
    | Blneg e => "(not " ++ string_of_bexp e ++ ")"
    | Bconj e1 e2 => "(and " ++ string_of_bexp e1 ++ " " ++ string_of_bexp e2 ++ ")"
    | Bdisj e1 e2 => "(or " ++ string_of_bexp e1 ++ " " ++ string_of_bexp e2 ++ ")"
    end.


  (* Agree *)

  Module MA := TypEnvAgree V TE VS.

  Lemma agree_exp_size E1 E2 e :
    MA.agree (vars_exp e) E1 E2 ->
    exp_size e E1 = exp_size e E2.
  Proof.
    elim: e => //=.
    - move=> v Hag. exact: (MA.agree_vsize_singleton Hag).
    - move=> op e IH Hag. rewrite (IH Hag). reflexivity.
    - move=> op e1 IH1 e2 IH2 Hag.
      rewrite (IH1 (MA.agree_union_set_l Hag)) (IH2 (MA.agree_union_set_r Hag)).
      reflexivity.
    - move=> b e1 IH1 e2 IH2 Hag. move: (MA.agree_union_set_r Hag) => {}Hag.
      rewrite (IH1 (MA.agree_union_set_l Hag)) (IH2 (MA.agree_union_set_r Hag)).
      reflexivity.
  Qed.

  Lemma agree_well_formed_exp E1 E2 e :
    MA.agree (vars_exp e) E1 E2 ->
    well_formed_exp e E1 = well_formed_exp e E2
  with agree_well_formed_bexp E1 E2 e :
    MA.agree (vars_bexp e) E1 E2 ->
    well_formed_bexp e E1 = well_formed_bexp e E2.
  Proof.
    - (* agree_well_formed_exp *)
      case: e; simpl.
      + move=> v Hag. exact: (MA.agree_mem_singleton Hag).
      + done.
      + move=> _ e Hag. exact: (agree_well_formed_exp _ _ _ Hag).
      + move=> op e1 e2 Hag.
        rewrite (agree_well_formed_exp _ _ _ (MA.agree_union_set_l Hag)).
        rewrite (agree_well_formed_exp _ _ _ (MA.agree_union_set_r Hag)).
        rewrite (agree_exp_size (MA.agree_union_set_l Hag)).
        rewrite (agree_exp_size (MA.agree_union_set_r Hag)).
        reflexivity.
      + move=> b e1 e2 Hag.
        rewrite (agree_well_formed_bexp _ _ _ (MA.agree_union_set_l Hag)).
        move: (MA.agree_union_set_r Hag) => {}Hag.
        rewrite (agree_well_formed_exp _ _ _ (MA.agree_union_set_l Hag)).
        rewrite (agree_well_formed_exp _ _ _ (MA.agree_union_set_r Hag)).
        rewrite (agree_exp_size (MA.agree_union_set_l Hag)).
        rewrite (agree_exp_size (MA.agree_union_set_r Hag)).
        reflexivity.
    - (* agree_well_formed_bexp *)
      case: e; simpl.
      + done.
      + done.
      + move=> _ e1 e2 Hag.
        rewrite (agree_well_formed_exp _ _ _ (MA.agree_union_set_l Hag)).
        rewrite (agree_well_formed_exp _ _ _ (MA.agree_union_set_r Hag)).
        rewrite (agree_exp_size (MA.agree_union_set_l Hag)).
        rewrite (agree_exp_size (MA.agree_union_set_r Hag)).
        reflexivity.
      + move=> e Hag. rewrite (agree_well_formed_bexp _ _ _ Hag).
        reflexivity.
      + move=> e1 e2 Hag.
        rewrite (agree_well_formed_bexp _ _ _ (MA.agree_union_set_l Hag)).
        rewrite (agree_well_formed_bexp _ _ _ (MA.agree_union_set_r Hag)).
        reflexivity.
      + move=> e1 e2 Hag.
        rewrite (agree_well_formed_bexp _ _ _ (MA.agree_union_set_l Hag)).
        rewrite (agree_well_formed_bexp _ _ _ (MA.agree_union_set_r Hag)).
        reflexivity.
  Qed.

End MakeQFBV.


Module QFBV := MakeQFBV SSAVarOrder SSAVarOrderPrinter SSAVS SSATE SSAStore.
Canonical eunop_eqType := Eval hnf in EqType QFBV.eunop QFBV.eunop_eqMixin.
Canonical ebinop_eqType := Eval hnf in EqType QFBV.ebinop QFBV.ebinop_eqMixin.
Canonical bbinop_eqType := Eval hnf in EqType QFBV.bbinop QFBV.bbinop_eqMixin.
Canonical exp_eqType := Eval hnf in EqType QFBV.exp QFBV.exp_eqMixin.
Canonical bexp_eqType := Eval hnf in EqType QFBV.bexp QFBV.bexp_eqMixin.
