
(** * Coq [OrderedType] as a structure [orderedType] *)

(**
   A structure [orderedType] is defined in the module [O].

   Lemmas from Coq about [OrderedType] are defined for [orderedType] in
   the following modules.
   - [OT]: lemmas and tactics from [OrdersTac]
   - [F]: lemmas from [OrderedType.OrderedTypeFacts]
   - [KO]: lemmas from [OrderedType.KeyOrderedType]
   - [OF]: lemmas from [OrdersFacts]

   Additional lemmas about [orderedType] are provided in the module [L],
   which includes lemmas from [F] and [OF].

   Several instances of [orderedType] are provided.
   - [prodOrderedType] for product types
   - [sumOrderedType] for sum types
   - [mathcompOrderedType] for math-comp [orderType]
   - [positiveOrderedType] for [positive]
   - [NOrderedType] for [N]
   - [ZOrderedType] for [Z]
   [orderType] for [nat] is provided by the coercion [nat2orderedType].

   The structure [orderedType] is wrapped in [Ordered] as Coq's [OrderedType].
   Modules of [Ordered] can be created by the following functor:
   - [HOT_as_OT]: instantiate a module of [Ordered] from an [orderedType]

   Similarly, the following functor is available for instantiating modules
   of [Orders.OrderedTypeFull]:
   - [HOT_as_OTF]: instantiate a module of [Orders.OrderedTypeFull] from an
                   [orderedType]

   For enumerating elements (may not be fully) in an [orderedType], a module
   type [OrderedWithDefaultSucc] is defined. In the module type, a default
   element and a successor function must be provided. Modules of
   [OrderedWithDefaultSucc] can be instantiated by the following functor:
   - [HOT_as_OT_WDS]: instantiate a module of [OrderedWithDefaultSucc] from an
                      [orderedType]
*)

From Coq Require Import OrderedType Bool Arith ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat ssrfun eqtype order choice.
From ssrlib Require Import Types Tactics ZAriths.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** ** orderedType: OrderedType with decidable equality *)

Declare Scope ordered_scope.
Delimit Scope ordered_scope with OT.

Local Open Scope ordered_scope.

(** Class definition *)

Module O.

  Module ClassDef.

    Structure mixin_of (t : Type) :=
      Mixin { eq : t -> t -> Prop
            ; lt : t -> t -> Prop
            ; le : t -> t -> Prop
            ; eq_refl : forall x, eq x x
            ; eq_sym : forall x y, eq x y -> eq y x
            ; eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z
            ; lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z
            ; lt_not_eq : forall x y : t, lt x y -> ~ eq x y
            ; le_lteq : forall x y : t, le x y <-> lt x y \/ eq x y
            ; compare : forall x y : t, Compare lt eq x y
            ; eq_dec : forall x y : t, { eq x y } + { ~ eq x y } }.
    Notation class_of := mixin_of (only parsing).

    Section Def.

      Structure type : Type := Pack { sort; _ : class_of sort }.

      Local Coercion sort : type >-> Sortclass.

      Variables (T : Type) (cT : type).

      Definition class := let: Pack _ c := cT return class_of cT in c.
      Definition clone := fun c & cT -> T & phant_id (@Pack T c) cT => Pack c.

    End Def.

  End ClassDef.

  Import ClassDef.

  Module Exports.

    Coercion sort : type >-> Sortclass.
    Notation orderedType := type.
    Notation OrderedTypeMixin := Mixin.
    Notation OrderedType t m := (@Pack t m).
    Notation "[ 'orderedTypeMixin' 'of' T ]" :=
      (class _ : mixin_of T)
        (at level 0, format "[ 'orderedTypeMixin'  'of'  T ]") : ordered_scope.
    Notation "[ 'orderedType' 'of' T 'for' C ]" :=
      (@clone T C _ idfun id)
        (at level 0, format "[ 'orderedType'  'of'  T  'for'  C ]") : ordered_scope.
    Notation "[ 'orderedType' 'of' T ]" :=
      (@clone T _ _ id id)
        (at level 0, format "[ 'orderedType'  'of'  T ]") : ordered_scope.

  End Exports.

  Import Exports.

  Section Definitions.
    Context {t : orderedType}.
    Definition eq := eq (class t).
    Definition lt := lt (class t).
    Definition le := le (class t).
    Lemma eq_refl : forall x, eq x x.
    Proof. exact: eq_refl. Qed.
    Lemma eq_sym : forall x y, eq x y -> eq y x.
    Proof. exact: eq_sym. Qed.
    Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
    Proof. exact: eq_trans. Qed.
    Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
    Proof. exact: lt_trans. Qed.
    Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
    Proof. exact: lt_not_eq. Qed.
    Lemma le_lteq : forall x y : t, le x y <-> lt x y \/ eq x y.
    Proof. exact: le_lteq. Qed.
    Definition compare : forall x y : t, Compare lt eq x y.
    Proof. exact: compare. Defined.
    Definition eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
    Proof. exact: eq_dec. Defined.
  End Definitions.

  #[global]
   Hint Unfold Symmetric : ordered_type.
  #[global]
   Hint Immediate eq_sym : ordered_type.
  #[global]
   Hint Resolve eq_refl eq_trans lt_not_eq lt_trans le_lteq : ordered_type.

End O.

Export O.Exports.
Import O.


(** Notations *)

Infix "==" := eq (at level 70, no associativity) : ordered_scope.
Notation "x == y :> T" := ((x : T) == (y : T)) (at level 70, y at next level) : ordered_scope.
Notation "x ~= y" := (~ (x == y)) (at level 70, no associativity) : ordered_scope.
Notation "x ~= y :> T" := (~ (x == y :> T)) (at level 70, y at next level, no associativity) : ordered_scope.
Infix "<" := lt : ordered_scope.
Notation "x < y :> T" := ((x : T) < (y : T)) (at level 70, y at next level) : ordered_scope.
Notation "x > y" := (y < x) (only parsing) : ordered_scope.
Notation "x > y :> T" := (y < x :> T) (at level 70, y at next level, only parsing) : ordered_scope.
Notation "x < y < z" := (x < y /\ y < z) : ordered_scope.
Infix "<=" := le : ordered_scope.
Notation "x <= y :> T" := ((x : T) <= (y : T)) (at level 70, y at next level) : ordered_scope.
Notation "x >= y" := (y <= x) (only parsing) : ordered_scope.
Notation "x >= y :> T" := (y <= x :> T) (at level 70, y at next level, only parsing) : ordered_scope.
Notation "x <= y <= z" := (x <= y /\ y <= z) : ordered_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : ordered_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : ordered_scope.
Infix "?=" := compare (at level 70, no associativity) : ordered_scope.
Notation "x ?= y :> T" := (@compare (ClassDef.class T) x y) (at level 70, y at next level, no associativity) : ordered_scope.

Notation oeq := O.eq (only parsing).
Notation olt := O.lt (only parsing).
Notation ole := O.le (only parsing).
Notation ogt := (flip O.lt) (only parsing).
Notation oge := (flip O.le) (only parsing).
Notation ocompare := (O.compare) (only parsing).
Notation oeq_dec := eq_dec (only parsing).


(** ** Lemmas from OrdersTac *)

Module OT.

  Section OrderFacts.

    Context {t : orderedType}.

    Lemma le_refl (x : t) : le x x.
    Proof. rewrite le_lteq. right. exact: eq_refl. Qed.

    Lemma lt_irrefl (x : t) : ~ lt x x.
    Proof. move=> H. move: (lt_not_eq H). apply; exact: eq_refl. Qed.

    Lemma le_antisym (x y : t) : x <= y -> y <= x -> x == y.
    Proof.
      rewrite !le_lteq. move=> [] H1 [] H2 //.
      - apply: False_ind. exact: (lt_irrefl (lt_trans H1 H2)).
      - apply: eq_sym. assumption.
    Qed.

    #[global]
     Instance eq_equiv : Equivalence (eq (t:=t)).
    Proof. split; [ exact eq_refl | exact eq_sym | exact eq_trans ]. Qed.

    #[global]
     Instance lt_strorder : StrictOrder (lt (t:=t)).
    Proof. split; [ exact lt_irrefl | exact lt_trans]. Qed.

    Lemma neq_sym (x y : t) : ~ x == y -> ~ y == x.
    Proof. by auto using eq_sym. Qed.

    Lemma lt_total (x y : t) : lt x y \/ eq x y \/ lt y x.
    Proof. by destruct (compare x y); auto. Qed.

    Lemma lt_eq (x y z : t) : lt x y -> eq y z -> lt x z.
    Proof.
      move=> H1 H2. destruct (compare x z) as [ Hlt | Heq | Hlt ]; auto.
      - elim: (lt_not_eq H1). exact: (eq_trans Heq (eq_sym H2)).
      - elim: (lt_not_eq (lt_trans Hlt H1)). exact: (eq_sym H2).
    Qed.

    Lemma eq_lt (x y z : t) : eq x y -> lt y z -> lt x z.
    Proof.
      move=> H1 H2. destruct (compare x z) as [ Hlt | Heq | Hlt ]; auto.
      - elim: (lt_not_eq H2). exact: (eq_trans (eq_sym H1) Heq).
      - elim: (lt_not_eq (lt_trans H2 Hlt)). exact: (eq_sym H1).
    Qed.

    #[global]
     Instance lt_compat : Proper (eq ==> (eq (t:=t)) ==> iff) lt.
    Proof.
      apply proper_sym_impl_iff_2; auto with *.
      move => x x' Hx y y' Hy H.
      apply eq_lt with x; first exact: (eq_sym Hx).
      by apply lt_eq with y; auto.
    Qed.

    #[global]
     Instance le_compat : Proper (eq ==> (eq (t:=t)) ==> iff) le.
    Proof.
      apply proper_sym_impl_iff_2; auto with *.
      move => x x' Hx y y' Hy H. rewrite !le_lteq in H *. case: H => H.
      - left. rewrite -Hx -Hy. assumption.
      - right. rewrite -Hx -Hy. assumption.
    Qed.

    Ltac subst_eqns :=
      match goal with
      | H : _ == _ |- _ => (rewrite H || rewrite <- H); clear H; subst_eqns
      | _ => idtac
      end.

    Definition interp_ord o :=
      match o with OEQ => eq (t:=t) | OLT => lt (t:=t) | OLE => le (t:=t) end.
    Local Infix "+" := trans_ord.
    Local Notation "#" := interp_ord.

    Lemma trans o o' x y z : #o x y -> #o' y z -> #(o + o') x z.
    Proof.
      by destruct o, o'; simpl;
      rewrite ?le_lteq; intuition auto;
      subst_eqns; eauto using (StrictOrder_Transitive x y z) with *.
    Qed.

    Definition eq_trans (x y z : t) : x == y -> y == z -> x == z := @trans OEQ OEQ x y z.
    Definition le_trans (x y z : t) : x <= y -> y <= z -> x <= z := @trans OLE OLE x y z.
    Definition lt_trans (x y z : t) : x < y -> y < z -> x < z := @trans OLT OLT x y z.
    Definition le_lt_trans (x y z : t) : x <= y -> y < z -> x < z := @trans OLE OLT x y z.
    Definition lt_le_trans (x y z : t) : x < y -> y <= z -> x < z := @trans OLT OLE x y z.
    Definition eq_le (x y z : t) : x == y -> y <= z -> x <= z := @trans OEQ OLE x y z.
    Definition le_eq (x y z : t) : x <= y -> y == z -> x <= z := @trans OLE OEQ x y z.

    Lemma eq_neq (x y z : t) : x == y -> ~ y == z -> ~ x == z.
    Proof. by eauto using eq_trans, eq_sym. Qed.

    Lemma neq_eq (x y z : t) : ~ x == y -> y == z -> ~ x == z.
    Proof. by eauto using eq_trans, eq_sym. Qed.

    Lemma not_neq_eq (x y : t) : ~ ~ x == y -> x == y.
    Proof.
      intros H. by destruct (lt_total x y) as [H'|[H'|H']]; auto;
                destruct H; intro H; rewrite H in H'; eapply lt_irrefl; eauto.
    Qed.

    Lemma not_ge_lt (x y : t) : ~ y <= x -> x < y.
    Proof.
      intros H. destruct (lt_total x y); auto.
      destruct H. rewrite le_lteq. intuition.
    Qed.

    Lemma not_gt_le (x y : t) : ~ y < x -> x <= y.
    Proof.
      intros H. rewrite le_lteq. by generalize (lt_total x y); intuition.
    Qed.

    Lemma le_neq_lt (x y : t) : x <= y -> ~ x == y -> x < y.
    Proof. by auto using not_ge_lt, le_antisym. Qed.

  End OrderFacts.

  Ltac order_rewr x eqn :=
    (* NB: we could use the real rewrite here, but proofs would be uglier. *)
    let rewr H t := generalize t; clear H; intro H
    in
    match goal with
    | H : x == _ |- _ => rewr H (eq_trans (eq_sym eqn) H); order_rewr x eqn
    | H : _ == x |- _ => rewr H (eq_trans H eqn); order_rewr x eqn
    | H : ~x == _ |- _ => rewr H (eq_neq (eq_sym eqn) H); order_rewr x eqn
    | H : ~_ == x |- _ => rewr H (neq_eq H eqn); order_rewr x eqn
    | H : x < _ |- _ => rewr H (eq_lt (eq_sym eqn) H); order_rewr x eqn
    | H : _ < x |- _ => rewr H (lt_eq H eqn); order_rewr x eqn
    | H : x <= _ |- _ => rewr H (eq_le (eq_sym eqn) H); order_rewr x eqn
    | H : _ <= x |- _ => rewr H (le_eq H eqn); order_rewr x eqn
    | _ => clear eqn
    end.

  Ltac order_eq x y eqn :=
    match x with
    | y => clear eqn
    | _ => change (interp_ord OEQ x y) in eqn; order_rewr x eqn
    end.

  Ltac order_prepare :=
    match goal with
    | H : ?A -> False |- _ => change (~A) in H; order_prepare
    | H : ~(?R ?x ?y) |- _ =>
        match R with
        | eq => fail 1 (* if already using [eq], we leave it this ways *)
        | _ => (change (~x==y) in H ||
                apply not_gt_le in H ||
                apply not_ge_lt in H ||
                clear H || fail 1); order_prepare
        end
    | H : ?R ?x ?y |- _ =>
        match R with
        | eq => fail 1
        | lt => fail 1
        | le => fail 1
        | _ => (change (x==y) in H ||
                change (x<y) in H ||
                change (x<=y) in H ||
                clear H || fail 1); order_prepare
        end
    | |- ~ _ => intro; order_prepare
    | |- _ ?x ?x =>
        exact (eq_refl x) || exact (le_refl x) || exfalso
    | _ =>
        (apply not_neq_eq; intro) ||
        (apply not_ge_lt; intro) ||
        (apply not_gt_le; intro) || exfalso
    end.

  Ltac order_loop :=
    match goal with
    (* First, successful situations *)
    | H : ?x < ?x |- _ => exact (lt_irrefl H)
    | H : ~ ?x == ?x |- _ => exact (H (eq_refl x))
    (* Second, useless hyps *)
    | H : ?x <= ?x |- _ => clear H; order_loop
    (* Third, we eliminate equalities *)
    | H : ?x == ?y |- _ => order_eq x y H; order_loop
    (* Simultaneous le and ge is eq *)
    | H1 : ?x <= ?y, H2 : ?y <= ?x |- _ =>
        generalize (le_antisym H1 H2); clear H1 H2; intro; order_loop
    (* Simultaneous le and ~eq is lt *)
    | H1: ?x <= ?y, H2: ~ ?x == ?y |- _ =>
        generalize (le_neq_lt H1 H2); clear H1 H2; intro; order_loop
    | H1: ?x <= ?y, H2: ~ ?y == ?x |- _ =>
        generalize (le_neq_lt H1 (neq_sym H2)); clear H1 H2; intro; order_loop
    (* Transitivity of lt and le *)
    | H1 : ?x < ?y, H2 : ?y < ?z |- _ =>
        match goal with
        | H : x < z |- _ => fail 1
        | _ => generalize (lt_trans H1 H2); intro; order_loop
        end
    | H1 : ?x <= ?y, H2 : ?y < ?z |- _ =>
        match goal with
        | H : x < z |- _ => fail 1
        | _ => generalize (le_lt_trans H1 H2); intro; order_loop
        end
    | H1 : ?x < ?y, H2 : ?y <= ?z |- _ =>
        match goal with
        | H : x < z |- _ => fail 1
        | _ => generalize (lt_le_trans H1 H2); intro; order_loop
        end
    | H1 : ?x <= ?y, H2 : ?y <= ?z |- _ =>
        match goal with
        | H : x <= z |- _ => fail 1
        | _ => generalize (le_trans H1 H2); intro; order_loop
        end
    | _ => idtac
    end.

  Ltac order :=
    intros; order_prepare; order_loop; fail "Order tactic unsuccessful".

End OT.

Notation oeq_ST := OT.eq_equiv.


(** ** eq_dec can be defined using compare *)

Module EqDec.

  Import OT.

  Section EqDec.

    Context {t : orderedType}.

    Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
    Proof with auto with ordered_type.
      intros x y; elim (compare x y); intro H; [ right | left | right ]...
      assert (~ eq y x)...
    Defined.

  End EqDec.

End EqDec.


(** ** Lemmas from OrderedType.OrderedTypeFacts *)

Module F.

  Local Close Scope boolean_if_scope.
  Local Open Scope general_if_scope.

  Import OT.

  Section OrderedType.

    Context {t : orderedType}.

    #[global]
     Instance eq_equiv : Equivalence (eq (t:=t)).
    Proof. split; [ exact eq_refl | exact eq_sym | exact eq_trans ]. Qed.

    Lemma lt_antirefl : forall (x : t), ~ lt x x.
    Proof.
      intros x; intro; absurd (eq x x); auto with ordered_type.
    Qed.

    #[global]
     Instance lt_strorder : StrictOrder (lt (t:=t)).
    Proof. split; [ exact lt_antirefl | exact lt_trans]. Qed.

    Lemma lt_eq : forall (x y z : t), lt x y -> eq y z -> lt x z.
    Proof with auto with ordered_type.
      intros x y z H ?; destruct (compare x z) as [Hlt|Heq|Hlt]; auto.
      elim (lt_not_eq H); apply eq_trans with z...
      elim (lt_not_eq (lt_trans Hlt H))...
    Qed.

    Lemma eq_lt : forall (x y z : t), eq x y -> lt y z -> lt x z.
    Proof with auto with ordered_type.
      intros x y z H H0; destruct (compare x z) as [Hlt|Heq|Hlt]; auto.
      elim (lt_not_eq H0); apply eq_trans with x...
      elim (lt_not_eq (lt_trans H0 Hlt))...
    Qed.

    #[global]
     Instance lt_compat : Proper (eq==>eq==>iff) (lt (t:=t)).
    apply proper_sym_impl_iff_2; auto with *.
    intros x x' Hx y y' Hy H.
    apply eq_lt with x; auto with ordered_type.
    apply lt_eq with y; auto.
    Qed.

    Lemma lt_total : forall (x y : t), lt x y \/ eq x y \/ lt y x.
    Proof. intros x y; destruct (compare x y); auto. Qed.

    Ltac order := OT.order.

    Lemma le_eq (x y z : t) : ~lt x y -> eq y z -> ~lt x z. Proof. order. Qed.
    Lemma eq_le (x y z : t) : eq x y -> ~lt y z -> ~lt x z. Proof. order. Qed.
    Lemma neq_eq (x y z : t) : ~eq x y -> eq y z -> ~eq x z. Proof. order. Qed.
    Lemma eq_neq (x y z : t) : eq x y -> ~eq y z -> ~eq x z. Proof. order. Qed.
    Lemma le_lt_trans (x y z : t) : ~lt y x -> lt y z -> lt x z. Proof. order. Qed.
    Lemma lt_le_trans (x y z : t) : lt x y -> ~lt z y -> lt x z. Proof. order. Qed.
    Lemma le_neq (x y : t) : ~lt x y -> ~eq x y -> lt y x. Proof. order. Qed.
    Lemma le_trans (x y z : t) : ~lt y x -> ~lt z y -> ~lt z x. Proof. order. Qed.
    Lemma le_antisym (x y : t) : ~lt y x -> ~lt x y -> eq x y. Proof. order. Qed.
    Lemma neq_sym (x y : t) : ~eq x y -> ~eq y x. Proof. order. Qed.
    Lemma lt_le (x y : t) : lt x y -> ~lt y x. Proof. order. Qed.
    Lemma gt_not_eq (x y : t) : lt y x -> ~ eq x y. Proof. order. Qed.
    Lemma eq_not_lt (x y : t) : eq x y -> ~ lt x y. Proof. order. Qed.
    Lemma eq_not_gt (x y : t) : eq x y -> ~ lt y x. Proof. order. Qed.
    Lemma lt_not_gt (x y : t) : lt x y -> ~ lt y x. Proof. order. Qed.

  End OrderedType.

  #[global]
   Hint Resolve gt_not_eq eq_not_lt : ordered_type.
  #[global]
   Hint Immediate eq_lt lt_eq le_eq eq_le neq_eq eq_neq : ordered_type.
  #[global]
   Hint Resolve eq_not_gt lt_irrefl lt_not_gt : ordered_type.

  Section OrderedType.

    Context {t : orderedType}.

    Lemma elim_compare_eq :
      forall x y : t,
        eq x y -> exists H : eq x y, compare x y = EQ H.
    Proof.
      intros x y H; case (compare x y); intros H'; try (exfalso; order).
      by exists H'; auto.
    Qed.

    Lemma elim_compare_lt :
      forall x y : t,
        lt x y -> exists H : lt x y, compare x y = LT H.
    Proof.
      intros x y H; case (compare x y); intros H'; try (exfalso; order).
      by exists H'; auto.
    Qed.

    Lemma elim_compare_gt :
      forall x y : t,
        lt y x -> exists H : lt y x, compare x y = GT H.
    Proof.
      intros x y H; case (compare x y); intros H'; try (exfalso; order).
      by exists H'; auto.
    Qed.

  End OrderedType.

  Ltac elim_comp :=
    match goal with
    | |- ?e => match e with
               | context ctx [ compare ?a ?b ] =>
                   let H := fresh in
                   (destruct (compare a b) as [H|H|H]; try order)
               end
    end.

  Ltac elim_comp_eq x y :=
    elim (elim_compare_eq (x:=x) (y:=y));
     [ intros _1 _2; rewrite _2; clear _1 _2 | auto ].

  Ltac elim_comp_lt x y :=
    elim (elim_compare_lt (x:=x) (y:=y));
     [ intros _1 _2; rewrite _2; clear _1 _2 | auto ].

  Ltac elim_comp_gt x y :=
    elim (elim_compare_gt (x:=x) (y:=y));
    [ intros _1 _2; rewrite _2; clear _1 _2 | auto ].

  Notation eq_dec := eq_dec.

  Section OrderedType.

    Context {t : orderedType}.

    Lemma lt_dec : forall x y : t, {lt x y} + {~ lt x y}.
    Proof.
      by intros x y; elim (compare x y); [ left | right | right ]; auto with ordered_type.
    Defined.

    Definition eqb (x y : t) : bool := if eq_dec x y then true else false.

    Lemma eqb_alt :
      forall x y, eqb x y = match compare x y with EQ _ => true | _ => false end.
    Proof.
      by unfold eqb; intros x y; destruct (eq_dec x y); elim_comp; auto.
    Qed.

    Lemma eqb_eq (x y : t) : eqb x y <-> eq x y.
    Proof. rewrite /eqb. by case: (eq_dec x y) => H //=. Qed.

  End OrderedType.

  Infix "=?" := eqb (at level 70, no associativity) : ordered_scope.
  Notation "x ~=? y" := (~~ eqb x y) (at level 70, no associativity) : ordered_scope.


  Section ForNotations.

    Context {t : orderedType}.

    Notation In := (InA (eq (t:=t))).
    Notation Inf := (lelistA (lt (t:=t))).
    Notation Sort := (Sorting.Sorted.sort (lt (t:=t))).
    Notation NoDup := (NoDupA (eq (t:=t))).

    Lemma In_eq : forall l x y, eq x y -> In x l -> In y l.
    Proof. exact (InA_eqA eq_equiv). Qed.

    Lemma ListIn_In : forall l x, List.In x l -> In x l.
    Proof. exact (In_InA eq_equiv). Qed.

    Lemma Inf_lt : forall l x y, lt x y -> Inf y l -> Inf x l.
    Proof. exact (InfA_ltA lt_strorder). Qed.

    Lemma Inf_eq : forall l x y, eq x y -> Inf y l -> Inf x l.
    Proof. exact (InfA_eqA eq_equiv lt_compat). Qed.

    Lemma Sort_Inf_In : forall l x a, Sort l -> Inf a l -> In x l -> lt a x.
    Proof. exact (SortA_InfA_InA eq_equiv lt_strorder lt_compat). Qed.

    Lemma ListIn_Inf : forall l x, (forall y, List.In y l -> lt x y) -> Inf x l.
    Proof. exact (@In_InfA t lt). Qed.

    Lemma In_Inf : forall l x, (forall y, In y l -> lt x y) -> Inf x l.
    Proof. exact (InA_InfA eq_equiv (ltA:=lt)). Qed.

    Lemma Inf_alt :
      forall l x, Sort l -> (Inf x l <-> (forall y, In y l -> lt x y)).
    Proof. exact (InfA_alt eq_equiv lt_strorder lt_compat). Qed.

    Lemma Sort_NoDup : forall l, Sort l -> NoDup l.
    Proof. exact (SortA_NoDupA eq_equiv lt_strorder lt_compat). Qed.

  End ForNotations.

  #[global]
   Hint Resolve ListIn_In Sort_NoDup Inf_lt : ordered_type.

  #[global]
   Hint Immediate In_eq Inf_lt : ordered_type.

End F.

Infix "=?" := F.eqb (at level 70, no associativity) : ordered_scope.
Notation "x ~=? y" := (~~ F.eqb x y) (at level 70, no associativity) : ordered_scope.
Notation oeqb := F.eqb (only parsing).


(** ** Lemmas from OrderedType.KeyOrderedType *)

Module KO.

  Section Elt.

    Context {t : orderedType}.
    Variable elt : Type.

    Notation key := t.

    Definition eqk (p p' : key * elt) := eq (fst p) (fst p').

    Definition eqke (p p':key * elt) :=
      eq (fst p) (fst p') /\ (snd p) = (snd p').

    Definition ltk (p p' : key * elt) := lt (fst p) (fst p').

    #[local]
     Hint Unfold eqk eqke ltk : ordered_type.

    #[local]
     Hint Extern 2 (eqke ?a ?b) => split : ordered_type.

    Lemma eqke_eqk : forall x x', eqke x x' -> eqk x x'.
    Proof.
      unfold eqk, eqke; intuition.
    Qed.

    Lemma ltk_right_r : forall x k e e', ltk x (k,e) -> ltk x (k,e').
    Proof. auto. Qed.

    Lemma ltk_right_l : forall x k e e', ltk (k,e) x -> ltk (k,e') x.
    Proof. auto. Qed.

    #[local]
     Hint Immediate ltk_right_r ltk_right_l : ordered_type.

    Lemma eqk_refl : forall e, eqk e e.
    Proof. auto with ordered_type. Qed.

    Lemma eqke_refl : forall e, eqke e e.
    Proof. auto with ordered_type. Qed.

    Lemma eqk_sym : forall e e', eqk e e' -> eqk e' e.
    Proof. auto with ordered_type. Qed.

    Lemma eqke_sym : forall e e', eqke e e' -> eqke e' e.
    Proof. unfold eqke; intuition. Qed.

    Lemma eqk_trans : forall e e' e'', eqk e e' -> eqk e' e'' -> eqk e e''.
    Proof. eauto with ordered_type. Qed.

    Lemma eqke_trans : forall e e' e'', eqke e e' -> eqke e' e'' -> eqke e e''.
    Proof.
      unfold eqke; intuition; [ eauto with ordered_type | congruence ].
    Qed.

    Lemma ltk_trans : forall e e' e'', ltk e e' -> ltk e' e'' -> ltk e e''.
    Proof. eauto with ordered_type. Qed.

    Lemma ltk_not_eqk : forall e e', ltk e e' -> ~ eqk e e'.
    Proof. unfold eqk, ltk; auto with ordered_type. Qed.

    Lemma ltk_not_eqke : forall e e', ltk e e' -> ~eqke e e'.
    Proof.
      unfold eqke, ltk; intuition; simpl in *; subst.
      match goal with H : lt _ _, H1 : eq _ _ |- _ => exact (lt_not_eq H H1) end.
    Qed.

    #[local]
     Hint Resolve eqk_trans eqke_trans eqk_refl eqke_refl : ordered_type.
    #[local]
     Hint Resolve ltk_trans ltk_not_eqk ltk_not_eqke : ordered_type.
    #[local]
     Hint Immediate eqk_sym eqke_sym : ordered_type.

    #[global]
     Instance eqk_equiv : Equivalence eqk.
    Proof. constructor; eauto with ordered_type. Qed.

    #[global]
     Instance eqke_equiv : Equivalence eqke.
    Proof. split; eauto with ordered_type. Qed.

    #[global]
     Instance ltk_strorder : StrictOrder ltk.
    Proof. constructor; eauto with ordered_type. intros x; apply (irreflexivity (x:=fst x)). Qed.

    #[global]
     Instance ltk_compat : Proper (eqk==>eqk==>iff) ltk.
    Proof.
      intros (x,e) (x',e') Hxx' (y,f) (y',f') Hyy'; compute.
      compute in Hxx'; compute in Hyy'.
      rewrite -> Hxx', Hyy'; auto.
    Qed.

    #[global]
     Instance ltk_compat' : Proper (eqke==>eqke==>iff) ltk.
    Proof.
      intros (x,e) (x',e') (Hxx',_) (y,f) (y',f') (Hyy',_); compute.
      compute in Hxx'; compute in Hyy'. rewrite -> Hxx', Hyy'; auto.
    Qed.

    (* Additional facts *)

    Lemma eqk_not_ltk : forall x x', eqk x x' -> ~ltk x x'.
    Proof.
      unfold eqk, ltk; simpl; auto with ordered_type.
    Qed.

    Lemma ltk_eqk : forall e e' e'', ltk e e' -> eqk e' e'' -> ltk e e''.
    Proof. eauto with ordered_type. Qed.

    Lemma eqk_ltk : forall e e' e'', eqk e e' -> ltk e' e'' -> ltk e e''.
    Proof.
      intros (k,e) (k',e') (k'',e'').
      unfold ltk, eqk; simpl; eauto with ordered_type.
    Qed.

    #[local]
     Hint Resolve eqk_not_ltk : ordered_type.
    #[local]
     Hint Immediate ltk_eqk eqk_ltk : ordered_type.

    Lemma InA_eqke_eqk :
      forall x m, InA eqke x m -> InA eqk x m.
    Proof.
      unfold eqke; induction 1; intuition.
    Qed.

    #[local]
     Hint Resolve InA_eqke_eqk : ordered_type.

    Definition MapsTo (k : key) (e : elt) := InA eqke (k, e).

    Definition In k m := exists e : elt, MapsTo k e m.

    Notation Sort := (Sorting.Sorted.sort ltk).

    Notation Inf := (lelistA ltk).

    #[local]
     Hint Unfold MapsTo In : ordered_type.

    (* An alternative formulation for [In k l] is [exists e, InA eqk (k,e) l] *)

    Lemma In_alt : forall k l, In k l <-> exists e, InA eqk (k,e) l.
    Proof with auto with ordered_type.
      intros k l; split; intros [y H].
      exists y...
      induction H as [a l eq|a l H IH].
      destruct a as [k' y'].
      exists y'...
      destruct IH as [e H0].
      exists e...
    Qed.

    Lemma MapsTo_eq : forall l x y e, eq x y -> MapsTo x e l -> MapsTo y e l.
    Proof.
      intros l x y e **; unfold MapsTo in *; apply InA_eqA with (x,e); eauto with *.
    Qed.

    Lemma In_eq : forall l x y, eq x y -> In x l -> In y l.
    Proof.
      destruct 2 as (e,E); exists e; eapply MapsTo_eq; eauto.
    Qed.

    Lemma Inf_eq : forall l x x', eqk x x' -> Inf x' l -> Inf x l.
    Proof. exact (InfA_eqA eqk_equiv ltk_compat). Qed.

    Lemma Inf_lt : forall l x x', ltk x x' -> Inf x' l -> Inf x l.
    Proof. exact (InfA_ltA ltk_strorder). Qed.

    #[local]
     Hint Immediate Inf_eq : ordered_type.
    #[local]
     Hint Resolve Inf_lt : ordered_type.

    Lemma Sort_Inf_In :
      forall l p q, Sort l -> Inf q l -> InA eqk p l -> ltk q p.
    Proof.
      exact (SortA_InfA_InA eqk_equiv ltk_strorder ltk_compat).
    Qed.

    Lemma Sort_Inf_NotIn :
      forall l k e, Sort l -> Inf (k,e) l ->  ~In k l.
    Proof.
      intros l k e H H0; red; intros H1.
      destruct H1 as [e' H2].
      elim (@ltk_not_eqk (k,e) (k,e')).
      eapply Sort_Inf_In; eauto with ordered_type.
      red; simpl; auto with ordered_type.
    Qed.

    Lemma Sort_NoDupA: forall l, Sort l -> NoDupA eqk l.
    Proof.
      exact (SortA_NoDupA eqk_equiv ltk_strorder ltk_compat).
    Qed.

    Lemma Sort_In_cons_1 : forall e l e', Sort (e::l) -> InA eqk e' l -> ltk e e'.
    Proof.
      inversion 1; intros; eapply Sort_Inf_In; eauto.
    Qed.

    Lemma Sort_In_cons_2 : forall l e e', Sort (e::l) -> InA eqk e' (e::l) ->
                                          ltk e e' \/ eqk e e'.
    Proof.
      intros l; inversion_clear 2; auto with ordered_type.
      left; apply Sort_In_cons_1 with l; auto.
    Qed.

    Lemma Sort_In_cons_3 :
      forall x l k e, Sort ((k,e)::l) -> In x l -> ~eq x k.
    Proof.
      inversion_clear 1 as [|? ? H0 H1]; red; intros H H2.
      destruct (Sort_Inf_NotIn H0 H1 (In_eq H2 H)).
    Qed.

    Lemma In_inv : forall k k' e l, In k ((k',e) :: l) -> eq k k' \/ In k l.
    Proof.
      inversion 1 as [? H0].
      inversion_clear H0 as [? ? H1|]; eauto with ordered_type.
      destruct H1; simpl in *; intuition.
    Qed.

    Lemma In_inv_2 : forall k k' e e' l,
        InA eqk (k, e) ((k', e') :: l) -> ~ eq k k' -> InA eqk (k, e) l.
    Proof.
      inversion_clear 1 as [? ? H0|? ? H0]; compute in H0; intuition.
    Qed.

    Lemma In_inv_3 : forall x x' l,
        InA eqke x (x' :: l) -> ~ eqk x x' -> InA eqke x l.
    Proof.
      inversion_clear 1 as [? ? H0|? ? H0]; compute in H0; intuition.
    Qed.

  End Elt.

  #[global]
   Hint Unfold eqk eqke ltk : ordered_type.
  #[global]
   Hint Extern 2 (eqke ?a ?b) => split : ordered_type.
  #[global]
   Hint Resolve eqk_trans eqke_trans eqk_refl eqke_refl : ordered_type.
  #[global]
   Hint Resolve ltk_trans ltk_not_eqk ltk_not_eqke : ordered_type.
  #[global]
   Hint Immediate eqk_sym eqke_sym : ordered_type.
  #[global]
   Hint Resolve eqk_not_ltk : ordered_type.
  #[global]
   Hint Immediate ltk_eqk eqk_ltk : ordered_type.
  #[global]
   Hint Resolve InA_eqke_eqk : ordered_type.
  #[global]
   Hint Unfold MapsTo In : ordered_type.
  #[global]
   Hint Immediate Inf_eq : ordered_type.
  #[global]
   Hint Resolve Inf_lt : ordered_type.
  #[global]
   Hint Resolve Sort_Inf_NotIn : ordered_type.
  #[global]
   Hint Resolve In_inv_2 In_inv_3 : ordered_type.

End KO.


(** ** Lemmas from OrdersFacts *)

Module OF.

  Local Close Scope boolean_if_scope.
  Local Open Scope general_if_scope.

  Import OT F.

  Ltac order := OT.order.
  Ltac iorder := intuition order.

  Section CompareFacts.

    Context {t : orderedType}.

    Definition compare (x y : t) : comparison :=
      match compare x y with
      | LT _ => Lt
      | EQ _ => Eq
      | GT _ => Gt
      end.

    Local Infix "?=" := compare (at level 70, no associativity).

    Lemma compare_spec : forall (x y : t), CompareSpec (x == y) (x < y) (y < x) (compare x y).
    Proof.
      move=> x y. rewrite /compare. case: (x ?= y)%OT => H.
      - by apply: CompLt.
      - by apply: CompEq.
      - by apply: CompGt.
    Qed.

    Lemma compare_eq_iff x y : (x ?= y) = Eq <-> x == y.
    Proof.
      by case compare_spec; intro H; split; try easy; intro EQ;
      contradict H; rewrite EQ; apply irreflexivity.
    Qed.

    Lemma compare_eq x y : (x ?= y) = Eq -> x == y.
    Proof. by apply compare_eq_iff. Qed.

    Lemma compare_lt_iff x y : (x ?= y) = Lt <-> x < y.
    Proof.
      by case compare_spec; intro H; split; try easy; intro LT;
      contradict LT; auto with ordered_type.
    Qed.

    Lemma compare_gt_iff x y : (x ?= y) = Gt <-> y < x.
    Proof.
      by case compare_spec; intro H; split; try easy; intro LT;
      contradict LT; auto with ordered_type.
    Qed.

    Lemma compare_nlt_iff x y : (x ?= y) <> Lt <-> ~ (x < y).
    Proof. by rewrite compare_lt_iff; intuition. Qed.

    Lemma compare_ngt_iff x y : (x ?= y) <> Gt <-> ~ (y < x).
    Proof. by rewrite compare_gt_iff; intuition. Qed.

    Hint Rewrite compare_eq_iff compare_lt_iff compare_gt_iff : order.

    #[global]
     Instance compare_compat : Proper (eq ==> eq ==> Logic.eq) compare.
    Proof.
      intros x x' Hxx' y y' Hyy'.
      case (compare_spec x' y'); autorewrite with order; now rewrite -> Hxx', Hyy'.
    Qed.

    Lemma compare_refl x : (x ?= x) = Eq.
    Proof.
      case compare_spec; intros; trivial; now elim irreflexivity with x.
    Qed.

    Lemma compare_antisym x y : (y ?= x) = CompOpp (x ?= y).
    Proof.
      case (compare_spec x y); simpl; autorewrite with order;
        trivial; now symmetry.
    Qed.

  End CompareFacts.


  Section OrderedTypeFullFacts.

    Context {t : orderedType}.

    #[global]
     Instance le_preorder : PreOrder (le (t:=t)).
    Proof. by split; red; order. Qed.

    #[global]
     Instance le_order : PartialOrder eq (le (t:=t)).
    Proof. by compute; iorder. Qed.

    Lemma le_not_gt_iff : forall (x y : t), x <= y <-> ~ y < x.
    Proof. by iorder. Qed.

     Lemma lt_not_ge_iff : forall (x y : t), x < y <-> ~ y <= x.
     Proof. by iorder. Qed.

     Lemma le_or_gt : forall (x y : t), x <= y \/ y < x.
     Proof. intros x y. rewrite le_lteq; destruct (compare_spec x y); auto. Qed.

     Lemma lt_or_ge : forall (x y : t), x < y \/ y <= x.
     Proof. intros x y. rewrite le_lteq; destruct (compare_spec x y); iorder. Qed.

     Lemma eq_is_le_ge : forall (x y : t), x == y <-> x <= y /\ y <= x.
     Proof. iorder. Qed.

     Lemma compare_le_iff (x y : t) : compare x y <> Gt <-> x <= y.
     Proof. rewrite le_not_gt_iff. apply compare_ngt_iff. Qed.

     Lemma compare_ge_iff (x y : t) : compare x y <> Lt <-> y <= x.
     Proof. rewrite le_not_gt_iff. apply compare_nlt_iff. Qed.

  End OrderedTypeFullFacts.


  Section OrderedTypeFacts.

    Context {t : orderedType}.

    Tactic Notation "elim_compare" constr(x) constr(y) :=
      destruct (compare_spec x y).

    Tactic Notation "elim_compare" constr(x) constr(y) "as" ident(h) :=
      destruct (compare_spec x y) as [h|h|h].

    Lemma if_eq_dec (x y : t) (B : Type) (b b' : B) :
      (if eq_dec x y then b else b') =
        (match compare x y with Eq => b | _ => b' end).
    Proof. destruct eq_dec; elim_compare x y; auto; order. Qed.

    Lemma eqb_alt' :
      forall (x y : t), eqb x y = match compare x y with Eq => true | _ => false end.
    Proof. unfold eqb; intros; apply if_eq_dec. Qed.

    #[global]
     Instance eqb_compat : Proper (eq ==> (eq (t:=t)) ==> Logic.eq) eqb.
    Proof.
      intros x x' Hxx' y y' Hyy'.
      rewrite -> 2 eqb_alt', Hxx', Hyy'; auto.
    Qed.

  End OrderedTypeFacts.


  Section CompareBasedOrderFacts.

    Context {t : orderedType}.

    Infix "?=" := compare.

    Lemma compare_nle_iff (x y : t) : (x ?= y) = Gt <-> ~ (x <= y).
    Proof.
      rewrite <- compare_le_iff.
      destruct compare; split; easy || now destruct 1.
    Qed.

    Lemma compare_nge_iff (x y : t) : (x ?= y) = Lt <-> ~ (y <= x).
    Proof. now rewrite <- compare_nle_iff, compare_antisym, CompOpp_iff. Qed.

    Lemma lt_eq_cases (n m : t) : n <= m <-> n < m \/ n == m.
    Proof.
      rewrite <- compare_lt_iff, <- compare_le_iff, <- compare_eq_iff.
      destruct (n ?= m); now intuition.
    Qed.

  End CompareBasedOrderFacts.

End OF.


(** ** Other operations *)

Section OO.

  Context {t : orderedType}.

  Definition ltb (x y : t) := match compare x y with LT _ => true | _ => false end.
  Definition leb (x y : t) := match compare x y with GT _ => false | _ => true end.

  Lemma ltb_lt (x y : t) : ltb x y <-> lt x y.
  Proof.
    unfold ltb. case: (x ?= y) => //=.
    - move=> Heq. split => //=. move=> Hlt. apply: False_ind. exact: (lt_not_eq Hlt Heq).
    - move=> Hlt. split => //=. move=> Heq'. apply: False_ind.
      move: (lt_trans Hlt Heq'). exact: F.lt_antirefl.
  Qed.

  Lemma leb_le (x y : t) : leb x y <-> le x y.
  Proof.
    unfold leb. case: (x ?= y) => //=.
    - move=> Hlt. split => //=. move=> _. apply/le_lteq. by left.
    - move=> Heq. split => //=. move=> _. rewrite Heq. exact: OT.le_refl.
    - move=> Hlt. split => //=. move=> /le_lteq Hle. case: Hle => H.
      + apply: False_ind. exact: (F.lt_antirefl (lt_trans Hlt H)).
      + rewrite H in Hlt. by elim: (F.lt_antirefl Hlt).
  Qed.

End OO.

Infix "<?" := ltb (at level 70, no associativity) : ordered_scope.
Infix "<=?" := leb (at level 70, no associativity) : ordered_scope.
Notation "x >? y" := (y <? x) (only parsing, at level 70, no associativity) : ordered_scope.
Notation "x >=? y" := (y <=? x) (only parsing, at level 70, no associativity) : ordered_scope.
Notation "x <? y <? z" := (x <? y /\ y <? z) (at level 70, y at next level) : ordered_scope.
Notation "x <=? y <=? z" := (x <=? y /\ y <=? z) (at level 70, y at next level) : ordered_scope.
Notation "x <=? y <? z" := (x <=? y /\ y <? z) (at level 70, y at next level) : ordered_scope.
Notation "x <? y <=? z" := (x <? y /\ y <=? z) (at level 70, y at next level) : ordered_scope.
Notation oltb := ltb (only parsing).
Notation oleb := leb (only parsing).
Notation ogtb := (flip ltb) (only parsing).
Notation ogeb := (flip leb) (only parsing).


(** ** OrderedType structure as OrderedType Module *)

Module Type HasSucc (Import T : Structures.OrderedType.OrderedType).
  Parameter succ : t -> t.
  Parameter lt_succ : forall (x : t), lt x (succ x).
End HasSucc.


Module Type Ordered <: Structures.OrderedType.OrderedType.
  Parameter T : orderedType.
  Definition t : Type := T.
  Definition eq : t -> t -> Prop := oeq.
  Definition lt : t -> t -> Prop := olt.
  Definition le : t -> t -> Prop := ole.
  Parameter eq_refl : forall x : t, eq x x.
  Parameter eq_sym : forall x y : t, eq x y -> eq y x.
  Parameter eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Parameter lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Parameter lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Parameter compare : forall x y : t, Compare lt eq x y.
  Parameter eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Parameter le_lteq : forall x y, le x y <-> lt x y \/ eq x y.
End Ordered.

Module Type OrderedWithDefaultSucc :=
  Ordered <+ HasDefault <+ HasSucc.


Module Type OrderedType.
  Parameter t : orderedType.
End OrderedType.

Module Type OrderedTypeWithDefaultSucc <: OrderedType.
  Parameter t : orderedType.
  Parameter default : t.
  Parameter succ : t -> t.
  Parameter lt_succ : forall (x : t), lt x (succ x).
End OrderedTypeWithDefaultSucc.


Module OT_as_O (O : OrderedType) <: Ordered.
  Definition T := O.t.
  Definition t : Type := O.t.
  Definition eq : t -> t -> Prop := oeq.
  Definition lt : t -> t -> Prop := olt.
  Definition le : t -> t -> Prop := ole.
  Definition eq_refl : forall x : t, eq x x := eq_refl.
  Definition eq_sym : forall x y : t, eq x y -> eq y x := eq_sym.
  Definition eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z := eq_trans.
  Definition eq_equiv : Equivalence eq := OT.eq_equiv.
  Definition lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z := lt_trans.
  Definition lt_not_eq : forall x y : t, lt x y -> ~ eq x y := lt_not_eq.
  Definition le_lteq : forall x y : t, le x y <-> lt x y \/ eq x y := le_lteq.
  Definition compare : forall x y : t, Compare lt eq x y := ocompare.
  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y} := eq_dec.
End OT_as_O.

Module OT_as_O_WDS (O : OrderedTypeWithDefaultSucc) <: OrderedWithDefaultSucc.
  Include OT_as_O O.
  Definition default : t := O.default.
  Definition succ : t -> t := O.succ.
  Definition lt_succ : forall (x : t), lt x (succ x) := O.lt_succ.
End OT_as_O_WDS.

Module OT_as_OTF (O : OrderedType) <: Structures.Orders.OrderedTypeFull.
  Definition t : Type := O.t.
  Definition eq : t -> t -> Prop := oeq.
  Definition eq_equiv : Equivalence eq := OT.eq_equiv.
  Definition lt : t -> t -> Prop := olt.
  Definition lt_strorder : StrictOrder lt := OT.lt_strorder.
  Definition lt_compat : Proper (eq ==> eq ==> iff) lt := OT.lt_compat.
  Definition compare : t -> t -> comparison := OF.compare.
  Definition compare_spec : forall x y : t, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y) := OF.compare_spec.
  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y} := eq_dec.
  Definition le : t -> t -> Prop := ole.
  Definition le_lteq : forall x y : t, le x y <-> lt x y \/ eq x y := le_lteq.
End OT_as_OTF.


(** ** Ordered elements are also eqType *)

Module EO.

  Module ClassDef.

    Structure mixin_of
              (t : Type)
              (oc : O.ClassDef.class_of t) (ec : Equality.class_of t)
              (ot := O.ClassDef.Pack oc) (et := Equality.Pack ec) :=
      Mixin { eq_eqop : forall (x y : t), @eq ot x y <-> @eq_op et x y }.

    Set Primitive Projections.
    Record class_of (T : Type) :=
      Class { obase : O.ClassDef.class_of T
            ; ebase : Equality.class_of T
            ; mixin : mixin_of obase ebase }.
    Unset Primitive Projections.

    Section Def.
      Structure type : Type := Pack { sort; _ : class_of sort }.
      Local Coercion sort : type >-> Sortclass.
      Local Coercion obase : class_of >-> O.ClassDef.class_of.
      Local Coercion ebase : class_of >-> Equality.class_of.
      Variables (T : Type) (cT : type).
      Definition class := let: Pack _ c := cT return class_of cT in c.
      Definition clone c of phant_id class c := @Pack T c.
      Definition orderedType := @O.ClassDef.Pack cT class.
      Definition eqType := @Equality.Pack cT class.
    End Def.
  End ClassDef.
  Import ClassDef.
  Module Exports.
    Coercion obase : class_of >-> O.ClassDef.class_of.
    Coercion ebase : class_of >-> Equality.class_of.
    Coercion mixin : class_of >-> mixin_of.
    Coercion sort : type >-> Sortclass.
    Coercion orderedType : type >-> O.ClassDef.type.
    #[global]
     Canonical orderedType.
    Coercion eqType : type >-> Equality.type.
    #[global]
     Canonical eqType.
    Notation eqOrderedType := type.
    Notation EqOrderedTypeMixin := Mixin.
    Notation EqOrderedType t m := (@Pack t m).
  End Exports.
  Import Exports.
  Section Definitions.
    Context {t : eqOrderedType}.
    Definition eq_eqop : forall (x y : t), (x == y)%OT <-> (x == y)%B := eq_eqop (class t).
    Lemma eq_eq : forall x y : t, (x == y)%OT <-> x = y.
    Proof.
      move=> x y. split.
      - move/eq_eqop. move/eqP. by apply.
      - move=> ->. exact: eq_refl.
    Qed.
    Lemma neq_eqop : forall x y : t, (x ~= y)%OT <-> x != y.
    Proof.
      move=> x y; split.
      - move=> H. apply/negP/eq_eqop. assumption.
      - move/negP/eq_eqop. by apply.
    Qed.
    Lemma eqb_eqop (x y : t) : (x =? y)%OT = (x == y)%B.
    Proof.
      case H: (x == y)%B.
      - move/eqtype.eqP: H => ->. apply/F.eqb_eq. reflexivity.
      - apply/negP => H1. apply/negPf: H. move/F.eqb_eq: H1 => /eq_eq ->.
        exact: eqxx.
    Qed.
    Lemma eqbP : forall x y : t, reflect (x = y) (x =? y)%OT.
    Proof.
      move=> x y. case H: (x =? y)%OT.
      - apply: ReflectT. move/F.eqb_eq: H => /eq_eq ->. reflexivity.
      - apply: ReflectF. move=> Heq. apply/negPf: H.
        apply/F.eqb_eq. apply/eq_eq. assumption.
    Qed.
    Lemma compare : forall x y : t, Compare (fun x y : t => ltb x y) eq_op x y.
    Proof.
      move=> x y. case Heq: (x =? y).
      - apply: EQ. rewrite -eqb_eqop. assumption.
      - case Hlt: (x <? y).
        + apply: LT. assumption.
        + apply: GT. apply/ltb_lt. apply: F.le_neq.
          * move=> /ltb_lt H. apply/negPf: Hlt. assumption.
          * move=> /F.eqb_eq H. apply/negPf: Heq. assumption.
    Qed.
  End Definitions.
End EO.

Export EO.Exports.

Notation oeq_eq := EO.eq_eq (only parsing).
Notation oeqbP := EO.eqbP (only parsing).


Module Type EqOrdered <: Ordered.
  Parameter ET : eqOrderedType.
  Definition T : orderedType := ET.
  Definition t : Type := T.
  Definition eq : t -> t -> Prop := oeq.
  Definition lt : t -> t -> Prop := olt.
  Definition le : t -> t -> Prop := ole.
  Parameter eq_refl : forall x : t, eq x x.
  Parameter eq_sym : forall x y : t, eq x y -> eq y x.
  Parameter eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Parameter lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Parameter lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Parameter compare : forall x y : t, Compare lt eq x y.
  Parameter eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Parameter le_lteq : forall x y, le x y <-> lt x y \/ eq x y.
End EqOrdered.

Module Type EqOrderedWithDefaultSucc := EqOrdered <+ HasDefault <+ HasSucc.

Module Type EqOrderedType.
  Parameter t : eqOrderedType.
End EqOrderedType.

Module Type EqOrderedTypeWithDefaultSucc <: EqOrderedType.
  Parameter t : eqOrderedType.
  Parameter default : t.
  Parameter succ : t -> t.
  Parameter lt_succ : forall (x : t), lt x (succ x).
End EqOrderedTypeWithDefaultSucc.

Module EOT_as_EO (O : EqOrderedType) <: EqOrdered.
  Definition ET := O.t.
  Module H <: OrderedType.
    Definition t : orderedType := O.t.
  End H.
  Include OT_as_O H.
End EOT_as_EO.

Module EOT_as_EO_WDS (O : EqOrderedTypeWithDefaultSucc) <: EqOrderedWithDefaultSucc.
  Include EOT_as_EO O.
  Definition default : t := O.default.
  Definition succ : t -> t := O.succ.
  Definition lt_succ : forall (x : t), lt x (succ x) := O.lt_succ.
End EOT_as_EO_WDS.


(** ** Other lemmas *)

Module L.

  Module Import OT := OT.
  Module Import F := F.
  Module KO := KO.
  Module Import OF := OF.

  Include F.
  Include OF.


  Section OrderedTypeLemmas.

    Context {t : orderedType}.

    Lemma eqP {x y : t} : reflect (eq x y) (eqb x y).
    Proof.
      rewrite /eqb. case: (eq_dec x y) => H /=.
      - by apply: ReflectT.
      - by apply: ReflectF.
    Qed.

    Lemma eqb_refl (x : t) : eqb x x.
    Proof. apply/eqP. reflexivity. Qed.

    Lemma eqb_sym (x y : t) : eqb x y = eqb y x.
    Proof.
      case Hyx: (eqb y x).
      - move/eqP: Hyx => ->. exact: eqb_refl.
      - apply/negP => Hxy. apply/negPf: Hyx. move/eqP: Hxy => ->.
        exact: eqb_refl.
    Qed.

    Lemma eqb_trans (x y z : t) : eqb x y -> eqb y z -> eqb x z.
    Proof.
      move=> /eqP Hxy /eqP Hyz. apply/eqP. exact: (eq_trans Hxy Hyz).
    Qed.

    #[global]
     Instance eqb_equiv : Equivalence (eqb (t:=t)).
    Proof.
      by split; [ exact eqb_refl | move=> x y H; rewrite eqb_sym; assumption | exact eqb_trans ].
    Qed.

    Lemma nlt_eqVlt_iff (x y : t) : (~ (x < y)) <-> ((x == y) \/ (y < x)).
    Proof.
      split; move=> H.
      - case/not_gt_le/lt_eq_cases: H => H.
        + by right.
        + left; by apply: eq_sym.
      - apply/le_not_gt_iff/lt_eq_cases. case: H => H.
        + right; by apply: eq_sym.
        + by left.
    Qed.

    Lemma lt_neqAlt_iff (x y : t) : (x < y) <-> (x ~= y) /\ (~ (y < x)).
    Proof.
      split; move=> H.
      - split. move: (gt_not_eq H).
        + exact: neq_sym.
        + exact: (lt_not_gt H).
      - case: H => [H1 H2]. exact: (le_neq H2 (neq_sym H1)).
    Qed.


    Section Injective.

      Context (A B : orderedType) (f : A -> B).

      Definition oinjective : Prop :=
        forall x y, oeq (f x) (f y) -> oeq x y.

    End Injective.


    Lemma ltP (x y : t) : reflect (lt x y) (ltb x y).
    Proof.
      case H: (ltb x y).
      - apply: ReflectT. by apply/ltb_lt.
      - apply: ReflectF. apply/ltb_lt. by apply/idP/negPf.
    Qed.

    Lemma leP (x y : t) : reflect (le x y) (leb x y).
    Proof.
      case H: (leb x y).
      - apply: ReflectT. by apply/leb_le.
      - apply: ReflectF. apply/leb_le. by apply/idP/negPf.
    Qed.

    Lemma leb_spec (x y : t) : BoolSpec (x <= y) (y < x) (x <=? y).
    Proof.
      case leP; constructor; trivial.
      now rewrite <- compare_lt_iff, compare_nge_iff.
    Qed.

    Lemma ltb_spec (x y : t) : BoolSpec (x<y) (y<=x) (x<?y).
    Proof.
      case ltP; constructor; trivial.
      now rewrite <- compare_le_iff, compare_ngt_iff.
    Qed.

    Lemma leb_nle (x y : t) : x <=? y = false <-> ~ (x <= y).
    Proof.
      now rewrite <- not_true_iff_false, <- leb_le.
    Qed.

    Lemma leb_gt (x y : t) : x <=? y = false <-> y < x.
    Proof.
      now rewrite -> leb_nle, <- compare_lt_iff, compare_nge_iff.
    Qed.

    Lemma ltb_nlt (x y : t) : x <? y = false <-> ~ (x < y).
    Proof.
      now rewrite <- not_true_iff_false, <- ltb_lt.
    Qed.

    Lemma ltb_ge (x y : t) : x <? y = false <-> y <= x.
    Proof.
      now rewrite -> ltb_nlt, <- compare_le_iff, compare_ngt_iff.
    Qed.

    Lemma leb_refl (x : t) : x <=? x.
    Proof. apply leb_le. apply lt_eq_cases. now right. Qed.

    Lemma leb_antisym (x y : t) : y <=? x = negb (x <? y).
    Proof.
      apply eq_true_iff_eq. fold (is_true (oleb y x)).
      now rewrite -> negb_true_iff, leb_le, ltb_ge.
    Qed.

    Lemma ltb_irrefl (x : t) : x <? x = false.
    Proof. apply ltb_ge. apply lt_eq_cases. now right. Qed.

    Lemma ltb_antisym (x y : t) : y <? x = negb (x <=? y).
    Proof.
      apply eq_true_iff_eq. fold (is_true (oltb y x)).
      now rewrite -> negb_true_iff, ltb_lt, leb_gt.
    Qed.

    Lemma ltb_trans (x y z : t) : (x <? y)%OT -> (y <? z)%OT -> (x <? z)%OT.
    Proof. move => /ltP Hxy /ltP Hyz. apply/ltP. by order. Qed.

    Lemma leb_trans (x y z : t) : (x <=? y)%OT -> (y <=? z)%OT -> (x <=? z)%OT.
    Proof. move => /leP Hxy /leP Hyz. apply/leP. by order. Qed.

    Lemma ltb_leb_trans (x y z : t) : (x <? y)%OT -> (y <=? z)%OT -> (x <? z)%OT.
    Proof. move => /ltP Hxy /leP Hyz. apply/ltP. by order. Qed.

    Lemma leb_ltb_trans (x y z : t) : (x <=? y)%OT -> (y <? z)%OT -> (x <? z)%OT.
    Proof. move => /leP Hxy /ltP Hyz. apply/ltP. by order. Qed.

    Lemma eqb_compare (x y : t) :
      (x =? y) = match compare x y with Eq => true | _ => false end.
    Proof.
      apply eq_true_iff_eq. fold (is_true (x =? y)).
      rewrite -> eqb_eq, <- compare_eq_iff.
      now destruct compare.
    Qed.

    Lemma ltb_compare (x y : t) :
      (x <? y) = match compare x y with Lt => true | _ => false end.
    Proof.
      apply eq_true_iff_eq. fold (is_true (oltb x y)).
      rewrite -> ltb_lt, <- compare_lt_iff.
      now destruct compare.
    Qed.

    Lemma leb_compare (x y : t) :
      (x <=? y) = match compare x y with Gt => false | _ => true end.
    Proof.
      apply eq_true_iff_eq. fold (is_true (oleb x y)).
      rewrite -> leb_le, <- compare_le_iff.
      now destruct compare.
    Qed.

  End OrderedTypeLemmas.

End L.

Notation oeqP := L.eqP.
Notation oltP := L.ltP.
Notation oleP := L.leP.


(** ** Product orders *)

Module ProdOrderedType.

  Import OT.

  Module Base.
    Section Def.
      Context {t1 t2 : orderedType}.
      Notation t := (prod t1 t2).
      Definition eq (x y : t) : Prop :=
        match x, y with
        | (x1, x2), (y1, y2) => oeq x1 y1 /\ oeq x2 y2
        end.
      Definition lt (x y : t) : Prop :=
        match x, y with
        | (x1, x2), (y1, y2) => olt x1 y1 \/ (oeq x1 y1 /\ olt x2 y2)
        end.
      Definition le (x y : t) : Prop :=
        match x, y with
        | (x1, x2), (y1, y2) => olt x1 y1 \/ (oeq x1 y1 /\ ole x2 y2)
        end.
      Lemma eq_refl : forall x : t, eq x x.
      Proof. case => x1 x2 /=. split; by auto with ordered_type. Qed.
      Lemma eq_sym : forall x y : t, eq x y -> eq y x.
      Proof. move=> [] x1 x2 [] y1 y2 /= [H1 H2]. split; by auto with ordered_type. Qed.
      Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
      Proof. move=> [] x1 x2 [] y1 y2 [] z1 z2 /= [H1 H2] [H3 H4]. split; by order. Qed.
      Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
      Proof.
        move=> [] x1 x2 [] y1 y2 [] z1 z2 /=.
        case => [H1 | [H1 H2]]; case => [H3 | [H3 H4]]; by eauto with ordered_type.
      Qed.
      Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
      Proof.
        move=> [] x1 x2 [] y1 y2 /=. case => [H1 | [H1 H2]] [H3 H4]; by order.
      Qed.
      Lemma le_lteq : forall x y : t, le x y <-> lt x y \/ eq x y.
      Proof.
        move=> [] x1 x2 [] y1 y2 /=. rewrite le_lteq.
        case_all; by eauto with ordered_type.
      Qed.
      Definition compare : forall x y : t, Compare lt eq x y.
      Proof.
        move=> [] x1 x2 [] y1 y2. case: (ocompare x1 y1) => Hc1.
        - apply: LT; by left.
        - case: (ocompare x2 y2) => Hc2.
          + apply: LT; right; by auto.
          + apply: EQ; by split.
          + apply: GT; right; by eauto with ordered_type.
        - apply: GT; by left.
      Defined.
      Lemma eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
      Proof.
        move=> [] x1 x2 [] y1 y2 /=.
        case: (eq_dec x1 y1) => H1; case: (eq_dec x2 y2) => H2; tauto.
      Qed.
    End Def.
  End Base.

  Import Base.

  Definition prodOrderedTypeMixin (t1 t2 : orderedType) :=
    @OrderedTypeMixin (prod t1 t2) eq lt le
                      eq_refl eq_sym eq_trans lt_trans
                      lt_not_eq le_lteq compare eq_dec.

  #[global]
   Canonical prodOrderedType (t1 t2 : orderedType) :=
    Eval hnf in OrderedType (prod t1 t2) (prodOrderedTypeMixin t1 t2).

End ProdOrderedType.

Export ProdOrderedType.

Module ProdEqOrderedType.

  Module Base.
    Section Def.
      Context {t1 t2 : eqOrderedType}.
      Notation t := (prod t1 t2).
      Lemma eq_eqop : forall (x y : t), (x == y)%OT <-> (x == y)%B.
      Proof.
        move=> [] x1 x2 [] y1 y2 /=. split.
        - case => /EO.eq_eqop /eqP -> /EO.eq_eqop /eqP ->. exact: eqxx.
        - move/eqP => [] -> ->. reflexivity.
      Qed.
    End Def.
  End Base.

  Import Base.

  Definition prodEqOrderedTypeMixin (t1 t2 : eqOrderedType) :=
    @EqOrderedTypeMixin (prod t1 t2) (prodOrderedTypeMixin t1 t2) (prod_eqMixin t1 t2) eq_eqop.

  #[global]
   Canonical prodEqOrderedType (t1 t2 : eqOrderedType) :=
    Eval hnf in EqOrderedType (prod t1 t2) (EO.ClassDef.Class (prodEqOrderedTypeMixin t1 t2)).

End ProdEqOrderedType.

Export ProdEqOrderedType.

Module ProdOrdered (O1 O2 : Ordered) <: Ordered with Definition T := prodOrderedType O1.T O2.T.
  Module H <: OrderedType.
    Definition t := prodOrderedType O1.T O2.T.
  End H.
  Include OT_as_O H.
End ProdOrdered.

Module ProdOrderedWithDefaultSucc (O1 O2 : OrderedWithDefaultSucc) <: OrderedWithDefaultSucc with Definition T := prodOrderedType O1.T O2.T.
  Include ProdOrdered O1 O2.
  Definition default : t := (O1.default, O2.default).
  Definition succ '(x, y) : t := (O1.succ x, y).
  Lemma lt_succ (x : t) : lt x (succ x).
  Proof.
    case: x => x y. rewrite /lt /succ /=. left. exact: O1.lt_succ.
  Qed.
End ProdOrderedWithDefaultSucc.

Module ProdEqOrdered (O1 O2 : EqOrdered) <: EqOrdered with Definition ET := prodEqOrderedType O1.ET O2.ET.
  Definition ET : eqOrderedType := prodEqOrderedType O1.ET O2.ET.
  Include ProdOrdered O1 O2.
End ProdEqOrdered.

Module ProdEqOrderedWithDefaultSucc (O1 O2 : EqOrderedWithDefaultSucc) <: EqOrderedWithDefaultSucc with Definition ET := prodEqOrderedType O1.ET O2.ET.
  Include ProdEqOrdered O1 O2.
  Definition default : t := (O1.default, O2.default).
  Definition succ '(x, y) : t := (O1.succ x, y).
  Lemma lt_succ (x : t) : lt x (succ x).
  Proof.
    case: x => x y. rewrite /lt /succ /=. left. exact: O1.lt_succ.
  Qed.
End ProdEqOrderedWithDefaultSucc.


(** ** Sum orders *)

Module SumOrderedType.

  Import OT.

  Module Base.
    Section Def.
      Context {t1 t2 : orderedType}.
      Notation t := (sum t1 t2).
      Definition eq (x y : t) : Prop :=
        match x, y with
        | inl x, inl y => oeq x y
        | inl _, inr _ => False
        | inr _, inl _ => False
        | inr x, inr y => oeq x y
        end.
      Definition lt (x y : t) : Prop :=
        match x, y with
        | inl x, inl y => olt x y
        | inl _, inr _ => True
        | inr _, inl _ => False
        | inr x, inr y => olt x y
        end.
      Definition le (x y : t) : Prop :=
        match x, y with
        | inl x, inl y => ole x y
        | inl _, inr _ => True
        | inr _, inl _ => False
        | inr x, inr y => ole x y
        end.
      Lemma eq_refl : forall x : t, eq x x.
      Proof. case => /=; by auto with ordered_type. Qed.
      Lemma eq_sym : forall x y : t, eq x y -> eq y x.
      Proof. move=> [] x [] y /=; by auto with ordered_type. Qed.
      Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
      Proof. move=> [] x [] y [] z //= *; by order. Qed.
      Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
      Proof. move=> [] x [] y [] z //=; by eauto with ordered_type. Qed.
      Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
      Proof. move=> [] x [] y //=; by eauto with ordered_type. Qed.
      Lemma le_lteq : forall x y : t, le x y <-> lt x y \/ eq x y.
      Proof. move=> [] x [] y //=; by [ eauto with ordered_type | tauto ]. Qed.
      Definition compare : forall x y : t, Compare lt eq x y.
      Proof.
        move=> [] x [] y /=.
        - case: (ocompare x y) => Hc.
          + apply: LT; assumption.
          + apply: EQ; assumption.
          + apply: GT; assumption.
        - by apply: LT.
        - by apply: GT.
        - case: (ocompare x y) => Hc.
          + apply: LT; assumption.
          + apply: EQ; assumption.
          + apply: GT; assumption.
      Defined.
      Lemma eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
      Proof.
        move=> [] x [] y /=.
        - exact: (eq_dec x y).
        - right; tauto.
        - right; tauto.
        - exact: (eq_dec x y).
      Qed.
    End Def.
  End Base.

  Import Base.

  Definition sumOrderedTypeMixin (t1 t2 : orderedType) :=
    @OrderedTypeMixin (sum t1 t2) eq lt le
                      eq_refl eq_sym eq_trans lt_trans
                      lt_not_eq le_lteq compare eq_dec.

  #[global]
   Canonical sumOrderedType (t1 t2 : orderedType) :=
    Eval hnf in OrderedType (sum t1 t2) (sumOrderedTypeMixin t1 t2).

End SumOrderedType.

Export SumOrderedType.

Module SumEqOrderedType.

  Module Base.
    Section Def.
      Context {t1 t2 : eqOrderedType}.
      Notation t := (sum t1 t2).
      Lemma eq_eqop : forall (x y : t), (x == y)%OT <-> (x == y)%B.
      Proof.
        move=> [] x [] y /=.
        - split => H.
          + move/EO.eq_eqop: H => /eqP ->. exact: eqxx.
          + rewrite (eqP H). reflexivity.
        - split => H.
          + by inversion H.
          + discriminate.
        - split => H.
          + by inversion H.
          + discriminate.
        - split => H.
          + move/EO.eq_eqop: H => /eqP ->. exact: eqxx.
          + rewrite (eqP H). reflexivity.
      Qed.
    End Def.
  End Base.

  Import Base.

  Definition sumEqOrderedTypeMixin (t1 t2 : eqOrderedType) :=
    @EqOrderedTypeMixin (sum t1 t2) (sumOrderedTypeMixin t1 t2) (sum_eqMixin t1 t2) eq_eqop.

  #[global]
   Canonical sumEqOrderedType (t1 t2 : eqOrderedType) :=
    Eval hnf in EqOrderedType (sum t1 t2) (EO.ClassDef.Class (sumEqOrderedTypeMixin t1 t2)).

End SumEqOrderedType.

Export SumEqOrderedType.

Module SumOrdered (O1 O2 : Ordered) <: Ordered with Definition T := sumOrderedType O1.T O2.T.
  Module H <: OrderedType.
    Definition t := sumOrderedType O1.T O2.T.
  End H.
  Include OT_as_O H.
End SumOrdered.

Module SumEqOrdered (O1 O2 : EqOrdered) <: EqOrdered with Definition ET := sumEqOrderedType O1.ET O2.ET.
  Definition ET := sumEqOrderedType O1.ET O2.ET.
  Include SumOrdered O1 O2.
End SumEqOrdered.


(** ** List of orderedType as predType *)

From ssrlib Require Import Lists.

Section ListPredType.

  Import F L.

  Context {t : eqOrderedType}.

  (* The following definitions require only orderedType but conflict with seq_predType in mathcomp *)
  (*
  Definition oin (s : list t) : pred t := fun x => existsb (oeqb x) s.
  Definition olist := list t.
  Identity Coercion list_of_olist : olist >-> list.
  Coercion pred_of_olist (s : olist) : {pred t} := oin s.
  #[global]
   Canonical olist_predType := PredType (pred_of_olist : list t -> pred t).
  #[global]
   Canonical oin_predType := PredType oin.
   *)

  Import seq.

  Ltac in2oin := rewrite /mem /= /in_mem /=.

  Lemma oin_cons x a (s : seq t) :
    x \in (a::s) = (x =? a) || (x \in s).
  Proof. rewrite in_cons. rewrite EO.eqb_eqop. reflexivity. Qed.

  Lemma oin_app x (s1 s2 : seq t) :
    x \in (s1 ++ s2) = (x \in s1) || (x \in s2).
  Proof. exact: mem_cat. Qed.

  Lemma oin_rcons x (s : seq t) a :
    x \in (rcons s a) = (x \in s) || (x =? a).
  Proof. rewrite Seqs.in_rcons. rewrite EO.eqb_eqop. reflexivity. Qed.

  Lemma inA_oin x (s : seq t) : (SetoidList.InA oeq x s) -> (x \in s).
  Proof.
    elim: s x => [| a s IH] x Hin /=.
    - by inversion Hin.
    - rewrite oin_cons. case/InA_cons: Hin => Hin.
      + by move/eqb_eq: Hin => ->.
      + by rewrite (IH _ Hin) orbT.
  Qed.

  Lemma oin_inA x (s : seq t) : (x \in s) -> (SetoidList.InA oeq x s).
  Proof.
    elim: s x => [| a s IH] x Hin //=. rewrite oin_cons in Hin.
    case/orP: Hin => Hin.
    - left. apply/eqP; assumption.
    - right. exact: (IH _ Hin).
  Qed.

  Lemma oinP x (s : seq t) : reflect (SetoidList.InA oeq x s) (x \in s).
  Proof.
    case Hin: (x \in s).
    - apply: ReflectT. exact: (oin_inA Hin).
    - apply: ReflectF. move=> H. apply/negPf: Hin. exact: (inA_oin H).
  Qed.

End ListPredType.

Notation "x '\in' A :> T" :=  (in_mem x (mem (A : T)))
                                (at level 70, no associativity, only parsing, A at next level).


(** ** mathcomp orderType as eqOrderedType (and hence orderedType) *)

Module MathCompOrderedType.

  Local Close Scope ordered_scope.

  Module Base.
    Section Def.
      Context {disp : unit}.
      Context {t : orderType disp}.
      Definition eq (x y : t) : Prop := eq_op x y.
      Definition lt (x y : t) : Prop := (x < y)%O.
      Definition le (x y : t) : Prop := (x <= y)%O.
      Definition ltb (x y : t) : bool := (x < y)%O.
      Definition leb (x y : t) : bool := (x <= y)%O.
      Definition eq_refl : forall x : t, eq x x := fun x : t => eqxx x.
      Lemma eq_sym : forall x y : t, eq x y -> eq y x.
      Proof. move=> x y H. rewrite /eq (eqtype.eq_sym). assumption. Qed.
      Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
      Proof.
        rewrite /eq => x y z Hxy Hyz. rewrite (eqP Hxy) (eqP Hyz).
        exact: eqxx.
      Qed.
      Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
      Proof. rewrite /lt => x y z. exact: Order.POrderTheory.lt_trans. Qed.
      Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
      Proof.
        rewrite /lt /eq => x y Hlt Heq. rewrite (eqP Heq) in Hlt.
        rewrite Order.POrderTheory.ltxx in Hlt. discriminate.
      Qed.
      Lemma le_lteq : forall x y : t, le x y <-> lt x y \/ eq x y.
      Proof.
        rewrite /le /lt /eq => x y. rewrite Order.POrderTheory.le_eqVlt.
        case_all; by eauto.
      Qed.
      Definition compare : forall x y : t, Compare lt eq x y.
      Proof.
        rewrite /lt /eq => x y. case Heq: (x == y)%EQ.
        - apply: EQ; assumption.
        - case Hlt: (x < y)%O.
          + apply: LT; assumption.
          + apply: GT. by rewrite Order.TotalTheory.ltNge Order.POrderTheory.le_eqVlt
                                  negb_orb Heq Hlt.
      Defined.
      Lemma eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
      Proof.
        move=> x y. case Hxy: (x == y).
        - left; exact: Hxy.
        - move/negP: Hxy => Hxy. right; exact: Hxy.
      Qed.
      Lemma ltb_lt (x y : t) : ltb x y <-> lt x y.
      Proof. tauto. Qed.
      Lemma leb_le (x y : t) : leb x y <-> le x y.
      Proof. tauto. Qed.
      Lemma eq_eqop (x y : t) : eq x y <-> (x == y)%B.
      Proof. tauto. Qed.
    End Def.
  End Base.

  Import Base.

  Definition mathcompOrderedTypeMixin (disp : unit) (t : orderType disp) :=
    @OrderedTypeMixin t eq lt le
                      eq_refl eq_sym eq_trans lt_trans
                      lt_not_eq le_lteq compare eq_dec.

  #[global]
   Canonical mathcompOrderedType (disp : unit) (t : orderType disp) :=
    Eval hnf in OrderedType t (mathcompOrderedTypeMixin t).

  Definition mathcompEqOrderedTypeMixin (disp : unit) (t : orderType disp) :=
    @EqOrderedTypeMixin t (mathcompOrderedTypeMixin t) (Order.Total.class t) eq_eqop.

  #[global]
   Canonical mathcompEqOrderedType (disp : unit) (t : orderType disp) :=
    Eval hnf in EqOrderedType t (EO.ClassDef.Class (mathcompEqOrderedTypeMixin t)).

End MathCompOrderedType.

Export MathCompOrderedType.
Coercion MathCompOrderedType.mathcompOrderedType : orderType >-> orderedType.
Coercion MathCompOrderedType.mathcompEqOrderedType : orderType >-> eqOrderedType.


(** ** Additional orderType Lemmas *)

Section OrderTypeLemmas.

  Local Close Scope ordered_scope.
  Context {disp : unit}.
  Context {t : orderType disp}.

  Lemma nlt_eqVlt (x y : t) : (~~ (x < y))%O = ((x == y) || (y < x))%O.
  Proof.
    case Heq: (x == y)%O => /=.
    - apply/negP => Hlt. move: (Order.POrderTheory.lt_eqF Hlt). by rewrite Heq.
    - rewrite -Order.TotalTheory.leNgt Order.POrderTheory.le_eqVlt eqtype.eq_sym Heq /=.
      reflexivity.
  Qed.

  Lemma lt_neqAlt (x y : t) : (x < y)%O = (x != y) && (~~ (y < x))%O.
  Proof. rewrite -Order.TotalTheory.leNgt. exact: Order.POrderTheory.lt_neqAle. Qed.

End OrderTypeLemmas.


(** ** Instances of orderedType, decidableOrderedType, Ordered, and DecidableOrdered *)

(** Coq's OrderedType as orderedType *)

Module CoqOrdered (O : Structures.OrderedType.OrderedType).

  Module Base.
    Definition le (x y : O.t) := O.lt x y \/ O.eq x y.
    Lemma le_lteq (x y : O.t) : le x y <-> O.lt x y \/ O.eq x y.
    Proof. reflexivity. Qed.
  End Base.

  Import Base.

  Definition mixin :=
    @OrderedTypeMixin O.t O.eq O.lt le
                      O.eq_refl O.eq_sym O.eq_trans O.lt_trans
                      O.lt_not_eq le_lteq O.compare O.eq_dec.

  #[global]
   Canonical t :=
    Eval hnf in OrderedType O.t mixin.

End CoqOrdered.

Module CoqOrdered_as_Ordered (Import O : Structures.OrderedType.OrderedType) <: Ordered.
  Module M := CoqOrdered O.
  Definition T : orderedType := M.t.
  Definition t : Type := T.
  Definition eq : t -> t -> Prop := oeq.
  Definition lt : t -> t -> Prop := olt.
  Definition le : t -> t -> Prop := ole.
  Definition eq_refl : forall x : t, eq x x := O.eq_refl.
  Definition eq_sym : forall x y : t, eq x y -> eq y x := O.eq_sym.
  Definition eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z := O.eq_trans.
  Definition lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z := O.lt_trans.
  Definition lt_not_eq : forall x y : t, lt x y -> ~ eq x y := O.lt_not_eq.
  Definition compare : forall x y : t, Compare lt eq x y := O.compare.
  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y} := O.eq_dec.
  Definition le_lteq : forall x y, le x y <-> lt x y \/ eq x y := O.le_lteq.
End CoqOrdered_as_Ordered.


(** Numbers that use Logic.eq for equality *)

Module N.

  (* nat *)

  Module NatOT.

    Definition natOrderedTypeMixin :=
      @OrderedTypeMixin nat Logic.eq Nat.lt Nat.le
                        Nat.eq_refl Nat.eq_sym Nat.eq_trans Nat.lt_trans
                        DecidableTypeEx.Nat_as_DT.lt_not_eq Nat.le_lteq
                        DecidableTypeEx.Nat_as_DT.compare Nat.eq_dec.

    #[global]
     Canonical natOrderedType :=
      Eval hnf in OrderedType nat natOrderedTypeMixin.

  End NatOT.

  Export NatOT.

  Module NatEOT.

    Lemma nat_eq_eqop (x y : nat) : (x == y)%OT <-> (x == y)%B.
    Proof. split; move/eqP => H; assumption. Qed.

    Definition natEqOrderedTypeMixin :=
      @EqOrderedTypeMixin nat natOrderedTypeMixin nat_eqMixin nat_eq_eqop.

    #[global]
     Canonical natEqOrderedType :=
      Eval hnf in EqOrderedType nat (EO.ClassDef.Class natEqOrderedTypeMixin).

  End NatEOT.

  Export NatEOT.

  Module NatOrderedType <: OrderedTypeWithDefaultSucc.
    Definition t : orderedType := natOrderedType.
    Definition default : t := 0%nat.
    Definition succ : t -> t := Nat.succ.
    Lemma lt_succ : forall (x : t), lt x (succ x).
    Proof. exact: Nat.lt_succ_diag_r. Qed.
  End NatOrderedType.

  Module NatEqOrderedType <: EqOrderedTypeWithDefaultSucc.
    Definition t : eqOrderedType := natEqOrderedType.
    Definition default : t := NatOrderedType.default.
    Definition succ : t -> t := NatOrderedType.succ.
    Definition lt_succ : forall (x : t), lt x (succ x) := NatOrderedType.lt_succ.
  End NatEqOrderedType.

  Module NatOrdered <: EqOrdered := EOT_as_EO_WDS NatEqOrderedType.


  (* positive *)

  Module PositiveOT.

    Definition positiveOrderedTypeMixin :=
      @OrderedTypeMixin positive Logic.eq Pos.lt Pos.le
                        Pos.eq_refl Pos.eq_sym Pos.eq_trans Pos.lt_trans
                        DecidableTypeEx.Positive_as_DT.lt_not_eq Pos.le_lteq
                        DecidableTypeEx.Positive_as_DT.compare Pos.eq_dec.

    #[global]
     Canonical positiveOrderedType :=
      Eval hnf in OrderedType positive positiveOrderedTypeMixin.

  End PositiveOT.

  Export PositiveOT.

  Module PositiveEOT.

    Lemma positive_eq_eqop (x y : positive) : (x == y)%OT <-> (x == y)%B.
    Proof. split; move/eqP => H; assumption. Qed.

    Definition positiveEqOrderedTypeMixin :=
      @EqOrderedTypeMixin positive positiveOrderedTypeMixin pos_eqMixin positive_eq_eqop.

    #[global]
     Canonical positiveEqOrderedType :=
      Eval hnf in EqOrderedType positive (EO.ClassDef.Class positiveEqOrderedTypeMixin).

  End PositiveEOT.

  Export PositiveEOT.

  Module PositiveOrderedType <: OrderedTypeWithDefaultSucc.
    Definition t : orderedType := positiveOrderedType.
    Definition default : t := 1%positive.
    Definition succ : t -> t := Pos.succ.
    Lemma lt_succ : forall (x : t), lt x (succ x).
    Proof. exact: Pos.lt_succ_diag_r. Qed.
  End PositiveOrderedType.

  Module PositiveEqOrderedType <: EqOrderedTypeWithDefaultSucc.
    Definition t : eqOrderedType := positiveEqOrderedType.
    Definition default : t := PositiveOrderedType.default.
    Definition succ : t -> t := PositiveOrderedType.succ.
    Definition lt_succ : forall (x : t), lt x (succ x) := PositiveOrderedType.lt_succ.
  End PositiveEqOrderedType.

  Module PositiveOrdered <: EqOrdered := EOT_as_EO_WDS PositiveEqOrderedType.


  (* N *)

  Module NOT.

    Definition NOrderedTypeMixin :=
      @OrderedTypeMixin N Logic.eq N.lt N.le
                        N.eq_refl N.eq_sym N.eq_trans N.lt_trans
                        DecidableTypeEx.N_as_DT.lt_not_eq N.le_lteq
                        DecidableTypeEx.N_as_DT.compare N.eq_dec.

    #[global]
     Canonical NOrderedType :=
      Eval hnf in OrderedType N NOrderedTypeMixin.

  End NOT.

  Export NOT.

  Module NEOT.

    Lemma N_eq_eqop (x y : N) : (x == y)%OT <-> (x == y)%B.
    Proof. split; move/eqP => H; assumption. Qed.

    Definition NEqOrderedTypeMixin :=
      @EqOrderedTypeMixin N NOrderedTypeMixin N_eqMixin N_eq_eqop.

    #[global]
     Canonical NEqOrderedType :=
      Eval hnf in EqOrderedType N (EO.ClassDef.Class NEqOrderedTypeMixin).

  End NEOT.

  Export NEOT.

  Module NOrderedType <: OrderedTypeWithDefaultSucc.
    Definition t : orderedType := NOrderedType.
    Definition default : t := 0%num.
    Definition succ : t -> t := N.succ.
    Lemma lt_succ : forall (x : t), lt x (succ x).
    Proof. exact: N.lt_succ_diag_r. Qed.
  End NOrderedType.

  Module NEqOrderedType <: EqOrderedTypeWithDefaultSucc.
    Definition t : eqOrderedType := NEqOrderedType.
    Definition default : t := NOrderedType.default.
    Definition succ : t -> t := NOrderedType.succ.
    Definition lt_succ : forall (x : t), lt x (succ x) := NOrderedType.lt_succ.
  End NEqOrderedType.

  Module NOrdered <: EqOrdered := EOT_as_EO_WDS NEqOrderedType.


  (* Z *)

  Module ZOT.

    Definition ZOrderedTypeMixin :=
      @OrderedTypeMixin Z Logic.eq Z.lt Z.le
                        Z.eq_refl Z.eq_sym Z.eq_trans Z.lt_trans
                        DecidableTypeEx.Z_as_DT.lt_not_eq Z.le_lteq
                        DecidableTypeEx.Z_as_DT.compare Z.eq_dec.

    #[global]
     Canonical ZOrderedType :=
      Eval hnf in OrderedType Z ZOrderedTypeMixin.

  End ZOT.

  Export ZOT.

  Module ZEOT.

    Lemma Z_eq_eqop (x y : Z) : (x == y)%OT <-> (x == y)%B.
    Proof. split; move/eqP => H; assumption. Qed.

    Definition ZEqOrderedTypeMixin :=
      @EqOrderedTypeMixin Z ZOrderedTypeMixin Z_eqMixin Z_eq_eqop.

    #[global]
     Canonical ZEqOrderedType :=
      Eval hnf in EqOrderedType Z (EO.ClassDef.Class ZEqOrderedTypeMixin).

  End ZEOT.

  Export ZEOT.

  Module ZOrderedType <: OrderedTypeWithDefaultSucc.
    Definition t : orderedType := ZOrderedType.
    Definition default : t := 0%Z.
    Definition succ : t -> t := Z.succ.
    Lemma lt_succ : forall (x : t), lt x (succ x).
    Proof. exact: Z.lt_succ_diag_r. Qed.
  End ZOrderedType.

  Module ZEqOrderedType <: EqOrderedTypeWithDefaultSucc.
    Definition t : eqOrderedType := ZEqOrderedType.
    Definition default : t := ZOrderedType.default.
    Definition succ : t -> t := ZOrderedType.succ.
    Definition lt_succ : forall (x : t), lt x (succ x) := ZOrderedType.lt_succ.
  End ZEqOrderedType.

  Module ZOrdered <: EqOrdered := EOT_as_EO_WDS ZEqOrderedType.

End N.


(** Numbers that use functions for equality, less-than, and less-than-or-equal-to *)

Module EN.

  (* Another definition of NatOrderedType where propositional comparisons
   and boolean comparisons are not distinguished *)

  Module NatOT.
    Definition natOrderedType : orderedType := Order.NatOrder.orderType.
    Definition natEqOrderedType : eqOrderedType := Order.NatOrder.orderType.

    (*
    Add the following coercion so that we can write [forall n : nat, (n <= n)%OT]
    instead of [forall n : nat, (n <= n :> mathcompOrderedType Order.NatOrder.orderType)%OT].
     *)
    Definition nat2orderedType : nat -> mathcompOrderedType Order.NatOrder.orderType := id.
    Coercion nat2orderedType : nat >-> O.ClassDef.sort.
  End NatOT.

  Export NatOT.

  Module NatOrderedType <: OrderedTypeWithDefaultSucc.
    Definition t : orderedType := natOrderedType.
    Definition default : t := 0%nat.
    Definition succ : t -> t := Nat.succ.
    Lemma lt_succ : forall (x : t), lt x (succ x).
    Proof. exact: ltnSn. Qed.
  End NatOrderedType.

  Module NatEqOrderedType <: EqOrderedTypeWithDefaultSucc.
    Definition t : eqOrderedType := natEqOrderedType.
    Definition default : t := NatOrderedType.default.
    Definition succ : t -> t := NatOrderedType.succ.
    Definition lt_succ : forall (x : t), lt x (succ x) := NatOrderedType.lt_succ.
  End NatEqOrderedType.

  Module NatOrdered <: EqOrdered := EOT_as_EO_WDS NatEqOrderedType.


  (* Another definition of PositiveOrderedType where propositional comparisons
   and boolean comparisons are not distinguished *)

  Module PositiveOT.

    Local Close Scope ordered_scope.

    Module Base.
      Local Open Scope positive_scope.
      Notation t := pos_eqType.
      Notation eq := (@eqtype.eq_op t).
      Notation lt := Pos.ltb.
      Notation le := Pos.leb.
      Notation eq_refl := (@eqtype.eq_refl t).
      Lemma eq_sym (x y : t) : (x == y)%EQ -> (y == x)%EQ.
      Proof. rewrite eqtype.eq_sym. by apply. Qed.
      Lemma eq_trans (x y z : t) : x == y -> y == z -> x == z.
      Proof. move => /eqP -> /eqP ->. exact: eqxx. Qed.
      Notation lt_trans := pos_ltb_trans.
      Lemma lt_not_eq (x y : t) : lt x y -> ~ x == y.
      Proof.
        move=> /pos_ltP Hlt /eqP Heq.
        exact: (DecidableTypeEx.Positive_as_DT.lt_not_eq _ _ Hlt Heq).
      Qed.
      Lemma le_lteq (x y : t) : le x y <-> lt x y \/ x == y.
      Proof.
        move: (Pos.le_lteq x y) => [H1 H2]. split => H.
        - move/pos_leP: H => H. case: (H1 H) => {}H.
          + left; apply/pos_ltP; assumption.
          + right; apply/eqP; assumption.
        - apply/pos_leP. apply: H2. case: H => H.
          + left; apply/pos_ltP; assumption.
          + right; apply/eqP; assumption.
      Qed.
      Lemma compare (x y : t) : Compare lt eq x y.
      Proof.
        case: (DecidableTypeEx.Positive_as_DT.compare x y) => H.
        - apply: LT; apply/pos_ltP; assumption.
        - apply: EQ; apply/eqP; assumption.
        - apply: GT; apply/pos_ltP; assumption.
      Defined.
      Lemma eq_dec (x y : t) : { eq x y } + { ~ eq x y }.
      Proof. by case: (x == y); eauto. Qed.
      Notation ltb := Pos.ltb.
      Notation leb := Pos.leb.
      Lemma ltb_lt (x y : t) : ltb x y <-> lt x y.
      Proof. tauto. Qed.
      Lemma leb_le (x y : t) : leb x y <-> le x y.
      Proof. tauto. Qed.
    End Base.

    Import Base.

    Definition positiveOrderedTypeMixin :=
      @OrderedTypeMixin positive eq lt le
                        eq_refl eq_sym eq_trans lt_trans
                        lt_not_eq le_lteq compare eq_dec.

    #[global]
     Canonical positiveOrderedType :=
      Eval hnf in OrderedType positive positiveOrderedTypeMixin.

  End PositiveOT.

  Export PositiveOT.

  Module PositiveEOT.

    Lemma positive_eq_eqop (x y : positive) : (x == y)%OT <-> (x == y)%B.
    Proof. tauto. Qed.

    Definition positiveEqOrderedTypeMixin :=
      @EqOrderedTypeMixin positive positiveOrderedTypeMixin pos_eqMixin positive_eq_eqop.

    #[global]
     Canonical positiveEqOrderedType :=
      Eval hnf in EqOrderedType positive (EO.ClassDef.Class positiveEqOrderedTypeMixin).

  End PositiveEOT.

  Export PositiveEOT.

  Module PositiveOrderedType <: OrderedTypeWithDefaultSucc.
    Definition t : orderedType := positiveOrderedType.
    Definition default : t := 1%positive.
    Definition succ : t -> t := Pos.succ.
    Lemma lt_succ : forall (x : t), lt x (succ x).
    Proof. move=> x. apply/pos_ltP. exact: Pos.lt_succ_diag_r. Qed.
  End PositiveOrderedType.

  Module PositiveEqOrderedType <: EqOrderedTypeWithDefaultSucc.
    Definition t : eqOrderedType := positiveEqOrderedType.
    Definition default : t := PositiveOrderedType.default.
    Definition succ : t -> t := PositiveOrderedType.succ.
    Definition lt_succ : forall (x : t), lt x (succ x) := PositiveOrderedType.lt_succ.
  End PositiveEqOrderedType.

  Module PositiveOrdered <: EqOrdered := EOT_as_EO_WDS PositiveEqOrderedType.


  (* Another definition of NOrderedType where propositional comparisons
   and boolean comparisons are not distinguished *)

  Module NOT.

    Local Close Scope ordered_scope.

    Module Base.
      Local Open Scope N_scope.
      Notation t := N_eqType.
      Notation eq := (@eqtype.eq_op t).
      Notation lt := N.ltb.
      Notation le := N.leb.
      Notation eq_refl := (@eqtype.eq_refl t).
      Lemma eq_sym (x y : t) : x == y -> y == x.
      Proof. rewrite eqtype.eq_sym. by apply. Qed.
      Lemma eq_trans (x y z : t) : x == y -> y == z -> x == z.
      Proof. move => /eqP -> /eqP ->. exact: eqxx. Qed.
      Definition lt_trans (x y z : t) := @Nltn_trans y x z.
      Lemma lt_not_eq (x y : t) : lt x y -> ~ x == y.
      Proof.
        move=> /N_ltP Hlt /eqP Heq.
        exact: (DecidableTypeEx.N_as_DT.lt_not_eq _ _ Hlt Heq).
      Qed.
      Lemma le_lteq (x y : t) : le x y <-> lt x y \/ x == y.
      Proof.
        move: (N.le_lteq x y) => [H1 H2]. split => H.
        - move/N_leP: H => H. case: (H1 H) => {}H.
          + left; apply/N_ltP; assumption.
          + right; apply/eqP; assumption.
        - apply/N_leP. apply: H2. case: H => H.
          + left; apply/N_ltP; assumption.
          + right; apply/eqP; assumption.
      Qed.
      Lemma compare (x y : t) : Compare lt eq x y.
      Proof.
        case: (DecidableTypeEx.N_as_DT.compare x y) => H.
        - apply: LT; apply/N_ltP; assumption.
        - apply: EQ; apply/eqP; assumption.
        - apply: GT; apply/N_ltP; assumption.
      Defined.
      Lemma eq_dec (x y : t) : { eq x y } + { ~ eq x y }.
      Proof. by case: (x == y); eauto. Qed.
      Notation ltb := N.ltb.
      Notation leb := N.leb.
      Lemma ltb_lt (x y : t) : ltb x y <-> lt x y.
      Proof. tauto. Qed.
      Lemma leb_le (x y : t) : leb x y <-> le x y.
      Proof. tauto. Qed.
    End Base.

    Import Base.

    Definition NOrderedTypeMixin :=
      @OrderedTypeMixin N eq lt le
                        eq_refl eq_sym eq_trans lt_trans
                        lt_not_eq le_lteq compare eq_dec.

    #[global]
     Canonical NOrderedType :=
      Eval hnf in OrderedType N NOrderedTypeMixin.

  End NOT.

  Export NOT.

  Module NEOT.

    Lemma N_eq_eqop (x y : N) : (x == y)%OT <-> (x == y)%B.
    Proof. tauto. Qed.

    Definition NEqOrderedTypeMixin :=
      @EqOrderedTypeMixin N NOrderedTypeMixin N_eqMixin N_eq_eqop.

    #[global]
     Canonical NEqOrderedType :=
      Eval hnf in EqOrderedType N (EO.ClassDef.Class NEqOrderedTypeMixin).

  End NEOT.

  Export NEOT.

  Module NOrderedType <: OrderedTypeWithDefaultSucc.
    Definition t : orderedType := NOrderedType.
    Definition default : t := 0%num.
    Definition succ : t -> t := N.succ.
    Lemma lt_succ : forall (x : t), lt x (succ x).
    Proof. move=> x. apply/N_ltP. exact: N.lt_succ_diag_r. Qed.
  End NOrderedType.

  Module NEqOrderedType <: EqOrderedTypeWithDefaultSucc.
    Definition t : eqOrderedType := NEqOrderedType.
    Definition default : t := NOrderedType.default.
    Definition succ : t -> t := NOrderedType.succ.
    Definition lt_succ : forall (x : t), lt x (succ x) := NOrderedType.lt_succ.
  End NEqOrderedType.

  Module NOrdered <: EqOrdered := EOT_as_EO_WDS NEqOrderedType.


  (* Another definition of ZOrderedType where propositional comparisons
   and boolean comparisons are not distinguished *)

  Module ZOT.

    Local Close Scope ordered_scope.

    Module Base.
      Local Open Scope Z_scope.
      Notation t := Z_eqType.
      Notation eq := (@eqtype.eq_op t).
      Notation lt := Z.ltb.
      Notation le := Z.leb.
      Notation eq_refl := (@eqtype.eq_refl t).
      Lemma eq_sym (x y : t) : x == y -> y == x.
      Proof. rewrite eqtype.eq_sym. by apply. Qed.
      Lemma eq_trans (x y z : t) : x == y -> y == z -> x == z.
      Proof. move => /eqP -> /eqP ->. exact: eqxx. Qed.
      Notation lt_trans := Z_ltb_trans.
      Lemma lt_not_eq (x y : t) : lt x y -> ~ x == y.
      Proof.
        move=> /Z_ltP Hlt /eqP Heq.
        exact: (DecidableTypeEx.Z_as_DT.lt_not_eq _ _ Hlt Heq).
      Qed.
      Lemma le_lteq (x y : t) : le x y <-> lt x y \/ x == y.
      Proof.
        move: (Z.le_lteq x y) => [H1 H2]. split => H.
        - move/Z_leP: H => H. case: (H1 H) => {}H.
          + left; apply/Z_ltP; assumption.
          + right; apply/eqP; assumption.
        - apply/Z_leP. apply: H2. case: H => H.
          + left; apply/Z_ltP; assumption.
          + right; apply/eqP; assumption.
      Qed.
      Lemma compare (x y : t) : Compare lt eq x y.
      Proof.
        case: (DecidableTypeEx.Z_as_DT.compare x y) => H.
        - apply: LT; apply/Z_ltP; assumption.
        - apply: EQ; apply/eqP; assumption.
        - apply: GT; apply/Z_ltP; assumption.
      Defined.
      Lemma eq_dec (x y : t) : { eq x y } + { ~ eq x y }.
      Proof. by case: (x == y); eauto. Qed.
      Notation ltb := Z.ltb.
      Notation leb := Z.leb.
      Lemma ltb_lt (x y : t) : ltb x y <-> lt x y.
      Proof. tauto. Qed.
      Lemma leb_le (x y : t) : leb x y <-> le x y.
      Proof. tauto. Qed.
    End Base.

    Import Base.

    Definition ZOrderedTypeMixin :=
      @OrderedTypeMixin Z eq lt le
                        eq_refl eq_sym eq_trans lt_trans
                        lt_not_eq le_lteq compare eq_dec.

    #[global]
     Canonical ZOrderedType :=
      Eval hnf in OrderedType Z ZOrderedTypeMixin.

  End ZOT.

  Export ZOT.

  Module ZEOT.

    Lemma Z_eq_eqop (x y : Z) : (x == y)%OT <-> (x == y)%B.
    Proof. tauto. Qed.

    Definition ZEqOrderedTypeMixin :=
      @EqOrderedTypeMixin Z ZOrderedTypeMixin Z_eqMixin Z_eq_eqop.

    #[global]
     Canonical ZEqOrderedType :=
      Eval hnf in EqOrderedType Z (EO.ClassDef.Class ZEqOrderedTypeMixin).

  End ZEOT.

  Export ZEOT.

  Module ZOrderedType <: OrderedTypeWithDefaultSucc.
    Definition t : orderedType := ZOrderedType.
    Definition default : t := 0%Z.
    Definition succ : t -> t := Z.succ.
    Lemma lt_succ : forall (x : t), lt x (succ x).
    Proof. move=> x. apply/Z_ltP. exact: Z.lt_succ_diag_r. Qed.
  End ZOrderedType.

  Module ZEqOrderedType <: EqOrderedTypeWithDefaultSucc.
    Definition t : eqOrderedType := ZEqOrderedType.
    Definition default : t := ZOrderedType.default.
    Definition succ : t -> t := ZOrderedType.succ.
    Definition lt_succ : forall (x : t), lt x (succ x) := ZOrderedType.lt_succ.
  End ZEqOrderedType.

  Module ZOrdered <: EqOrdered := EOT_as_EO_WDS ZEqOrderedType.

End EN.


(** ** Sequences of orderedType *)

Module SeqOrderedType.

  Import seq.

  Module Base.
    Section Def.
      Context {e : orderedType}.
      Notation t := (seq e).
      Fixpoint eq (xs ys : t) : Prop :=
        match xs, ys with
        | [::], [::] => True
        | x::xs, y::ys => (x == y)%OT /\ (eq xs ys)
        | _, _ => False
        end.
      Fixpoint lt (xs ys : t) : Prop :=
        match xs, ys with
        | _, [::] => False
        | [::], _::_ => True
        | x::xs, y::ys => (x < y)%OT \/ ((x == y)%OT /\ (lt xs ys))
        end.
      Fixpoint le (xs ys : t) : Prop :=
        match xs, ys with
        | [::], _ => True
        | _, [::] => False
        | x::xs, y::ys => (x < y)%OT \/ ((x == y)%OT /\ (le xs ys))
        end.
      Lemma eq_refl (xs : t) : eq xs xs.
      Proof.
        elim: xs => [| x xs IH] //=. split; last assumption. reflexivity.
      Qed.
      Lemma eq_sym (xs ys : t) : eq xs ys -> eq ys xs.
      Proof.
        elim: xs ys => [| x xs IH] [| y ys] //=.
        move=> [Hx Hxs]. split; [ exact: (eq_sym Hx) | exact: (IH _ Hxs) ].
      Qed.
      Lemma eq_trans (xs ys zs : t) : eq xs ys -> eq ys zs -> eq xs zs.
      Proof.
        elim: xs ys zs => [| x xs IH] [| y ys] [| z zs] //=.
        move=> [Hx Hxs] [Hy Hys]. split; [ exact: (eq_trans Hx Hy) | exact: (IH _ _ Hxs Hys) ].
      Qed.
      Lemma lt_trans (xs ys zs : t) : lt xs ys -> lt ys zs -> lt xs zs.
      Proof.
        elim: xs ys zs => [| x xs IH] [| y ys] [| z zs] //=.
        case => Hx; case => Hy.
        - left. exact: (lt_trans Hx Hy).
        - move: Hy => [Hy1 Hy2]. left. rewrite -Hy1. assumption.
        - move: Hx => [Hx1 Hx2]. left. rewrite Hx1. assumption.
        - move: Hx Hy => [Hx1 Hx2] [Hy1 Hy2]. right.
          split; [ exact: (O.eq_trans Hx1 Hy1) | exact: (IH _ _ Hx2 Hy2) ].
      Qed.
      Lemma lt_not_eq (xs ys : t) : lt xs ys -> (~ eq xs ys).
      Proof.
        elim: xs ys => [| x xs IH] [| y ys] //=.
        - tauto.
        - case => H [Hx Hxs].
          + exact: (O.lt_not_eq H Hx).
          + apply: (IH _ _ Hxs). tauto.
      Qed.
      Lemma le_lteq (xs ys : t) : le xs ys <-> lt xs ys \/ eq xs ys.
      Proof.
        elim: xs ys => [| x xs IH] [| y ys]; simpl; try tauto.
        split.
        - case => H.
          + by left; left.
          + move: H => [Hx Hxs]. case/IH: Hxs => Hxs.
            * by left; right.
            * by right.
        - case => H; [ case: H => H |].
          + by left.
          + move: H => [Hx Hxs]. right; split; first assumption.
            apply/IH. by left.
          + move: H => [Hx Hxs]. right; split; first assumption.
            apply/IH. by right.
      Qed.
      Definition compare (xs ys : t) : Compare lt eq xs ys.
        elim: xs ys => [| x xs IH] [| y ys].
        - by apply: EQ.
        - by apply: LT.
        - by apply: GT.
        - case: (compare x y) => Hxy.
          + apply: LT. by left.
          + case: (IH ys) => Hxs.
            * apply: LT. by right.
            * by apply: EQ.
            * apply: GT. right. move: (O.eq_sym Hxy) => Hyx. tauto.
          + apply: GT. by left.
      Defined.
      Lemma eq_dec (xs ys : t) : {eq xs ys} + {~ eq xs ys}.
      Proof.
        case: (compare xs ys) => H.
        - right => Heq. exact: (lt_not_eq H Heq).
        - by left.
        - right => Heq. exact: (lt_not_eq H (eq_sym Heq)).
      Qed.
    End Def.
  End Base.

  Import Base.

  Section Exports.

    Context (t : orderedType).

    Definition seqOrderedTypeMixin :=
      @OrderedTypeMixin (seq t) eq lt le
                        eq_refl eq_sym eq_trans lt_trans
                        lt_not_eq le_lteq compare eq_dec.

    #[global]
     Canonical seqOrderedType :=
      Eval hnf in OrderedType (seq t) seqOrderedTypeMixin.

  End Exports.

End SeqOrderedType.

Export SeqOrderedType.

Module SeqEqOrderedType.
  Import seq.
  Section Aux.
    Context {t: eqOrderedType}.
    Lemma seq_eq_eqop (xs ys : seq t) : (xs == ys)%OT <-> (xs == ys)%B.
    Proof.
      elim: xs ys => [| x xs IH] [| y ys] //=. split.
      - case => /EO.eq_eq -> /IH /eqP ->. exact: eqxx.
      - move/eqP => [] -> ->. reflexivity.
    Qed.
  End Aux.
  Definition seqEqOrderedTypeMixin (t : eqOrderedType) :=
    @EqOrderedTypeMixin (seq t) (seqOrderedTypeMixin t) (seq_eqMixin t) seq_eq_eqop.
  #[global]
   Canonical seqEqOrderedType (t : eqOrderedType) :=
    Eval hnf in EqOrderedType (seq t) (EO.ClassDef.Class (seqEqOrderedTypeMixin t)).
End SeqEqOrderedType.
Export SeqEqOrderedType.

Module SeqOrdered (H : OrderedType) <: Ordered.
  Import seq.
  Module HH <: OrderedType.
    Definition t : orderedType := seqOrderedType H.t.
  End HH.
  Include OT_as_O HH.
End SeqOrdered.

Module SeqEqOrdered (H : EqOrderedType) <: EqOrdered.
  Import seq.
  Module HH <: EqOrderedType.
    Definition t : eqOrderedType := seqEqOrderedType H.t.
  End HH.
  Include EOT_as_EO HH.
End SeqEqOrdered.
