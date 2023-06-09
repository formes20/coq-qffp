
(** * General tactics *)

From Coq Require Import Bool.
From mathcomp Require Import ssreflect ssrbool eqtype.

Ltac dcase t := move: (refl_equal t); generalize t at -1.

(* Split goal of the form (_ && _). *)
Ltac splitb := apply/andP; split.

(* Split all hypotheses of the form (_ && _). *)
Ltac hyps_splitb :=
  repeat (match goal with
          | H: is_true (_ && _) |- _ =>
            let H1 := fresh in
            let H2 := fresh in
            move/andP: H => [H1 H2]
          | H: _ && _ = true |- _ =>
            let H1 := fresh in
            let H2 := fresh in
            move/andP: H => [H1 H2]
          end).

Ltac leftb := apply/orP; left.

Ltac rightb := apply/orP; right.

Ltac case_option :=
  repeat
    match goal with
    | H : Some _ = None |- _ => discriminate
    | H : None = Some _ |- _ => discriminate
    | H : Some (_, _, _, _, _, _, _, _, _, _) = Some (_, _, _, _, _, _, _, _, _, _) |- _ =>
        let H1 := fresh in
        let H2 := fresh in
        let H3 := fresh in
        let H4 := fresh in
        let H5 := fresh in
        let H6 := fresh in
        let H7 := fresh in
        let H8 := fresh in
        let H9 := fresh in
        let H0 := fresh in
        case: H; move=> H1 H2 H3 H4 H5 H6 H7 H8 H9 H0
    | H : Some (_, _, _, _, _, _, _, _, _) = Some (_, _, _, _, _, _, _, _, _) |- _ =>
        let H1 := fresh in
        let H2 := fresh in
        let H3 := fresh in
        let H4 := fresh in
        let H5 := fresh in
        let H6 := fresh in
        let H7 := fresh in
        let H8 := fresh in
        let H9 := fresh in
        case: H; move=> H1 H2 H3 H4 H5 H6 H7 H8 H9
    | H : Some (_, _, _, _, _, _, _, _) = Some (_, _, _, _, _, _, _, _) |- _ =>
        let H1 := fresh in
        let H2 := fresh in
        let H3 := fresh in
        let H4 := fresh in
        let H5 := fresh in
        let H6 := fresh in
        let H7 := fresh in
        let H8 := fresh in
        case: H; move=> H1 H2 H3 H4 H5 H6 H7 H8
    | H : Some (_, _, _, _, _, _, _) = Some (_, _, _, _, _, _, _) |- _ =>
        let H1 := fresh in
        let H2 := fresh in
        let H3 := fresh in
        let H4 := fresh in
        let H5 := fresh in
        let H6 := fresh in
        let H7 := fresh in
        case: H; move=> H1 H2 H3 H4 H5 H6 H7
    | H : Some (_, _, _, _, _, _) = Some (_, _, _, _, _, _) |- _ =>
        let H1 := fresh in
        let H2 := fresh in
        let H3 := fresh in
        let H4 := fresh in
        let H5 := fresh in
        let H6 := fresh in
        case: H; move=> H1 H2 H3 H4 H5 H6
    | H : Some (_, _, _, _, _) = Some (_, _, _, _, _) |- _ =>
        let H1 := fresh in
        let H2 := fresh in
        let H3 := fresh in
        let H4 := fresh in
        let H5 := fresh in
        case: H; move=> H1 H2 H3 H4 H5
    | H : Some (_, _, _, _) = Some (_, _, _, _) |- _ =>
        let H1 := fresh in
        let H2 := fresh in
        let H3 := fresh in
        let H4 := fresh in
        case: H; move=> H1 H2 H3 H4
    | H : Some (_, _, _) = Some (_, _, _) |- _ =>
        let H1 := fresh in
        let H2 := fresh in
        let H3 := fresh in
        case: H; move=> H1 H2 H3
    | H : Some (_, _) = Some (_, _) |- _ =>
        let H1 := fresh in
        let H2 := fresh in
        case: H; move=> H1 H2
    | H : Some _ = Some _ |- _ =>
        case: H; move=> H
    end.

Ltac case_tuples :=
  repeat match goal with
         | H : (_, _, _, _, _, _, _, _, _, _) = (_, _, _, _, _, _, _, _, _, _) |- _ =>
             let H1 := fresh in
             let H2 := fresh in
             let H3 := fresh in
             let H4 := fresh in
             let H5 := fresh in
             let H6 := fresh in
             let H7 := fresh in
             let H8 := fresh in
             let H9 := fresh in
             let H0 := fresh in
             case: H; move=> H1 H2 H3 H4 H5 H6 H7 H8 H9 H0
         | H : (_, _, _, _, _, _, _, _, _) = (_, _, _, _, _, _, _, _, _) |- _ =>
             let H1 := fresh in
             let H2 := fresh in
             let H3 := fresh in
             let H4 := fresh in
             let H5 := fresh in
             let H6 := fresh in
             let H7 := fresh in
             let H8 := fresh in
             let H9 := fresh in
             case: H; move=> H1 H2 H3 H4 H5 H6 H7 H8 H9
         | H : (_, _, _, _, _, _, _, _) = (_, _, _, _, _, _, _, _) |- _ =>
             let H1 := fresh in
             let H2 := fresh in
             let H3 := fresh in
             let H4 := fresh in
             let H5 := fresh in
             let H6 := fresh in
             let H7 := fresh in
             let H8 := fresh in
             case: H; move=> H1 H2 H3 H4 H5 H6 H7 H8
         | H : (_, _, _, _, _, _, _) = (_, _, _, _, _, _, _) |- _ =>
             let H1 := fresh in
             let H2 := fresh in
             let H3 := fresh in
             let H4 := fresh in
             let H5 := fresh in
             let H6 := fresh in
             let H7 := fresh in
             case: H; move=> H1 H2 H3 H4 H5 H6 H7
         | H : (_, _, _, _, _, _) = (_, _, _, _, _, _) |- _ =>
             let H1 := fresh in
             let H2 := fresh in
             let H3 := fresh in
             let H4 := fresh in
             let H5 := fresh in
             let H6 := fresh in
             case: H; move=> H1 H2 H3 H4 H5 H6
         | H : (_, _, _, _, _) = (_, _, _, _, _) |- _ =>
             let H1 := fresh in
             let H2 := fresh in
             let H3 := fresh in
             let H4 := fresh in
             let H5 := fresh in
             case: H; move=> H1 H2 H3 H4 H5
         | H : (_, _, _, _) = (_, _, _, _) |- _ =>
             let H1 := fresh in
             let H2 := fresh in
             let H3 := fresh in
             let H4 := fresh in
             case: H; move=> H1 H2 H3 H4
         | H : (_, _, _) = (_, _, _) |- _ =>
             let H1 := fresh in
             let H2 := fresh in
             let H3 := fresh in
             case: H; move=> H1 H2 H3
         | H : (_, _) = (_, _) |- _ =>
             let H1 := fresh in
             let H2 := fresh in
             case: H; move=> H1 H2
         end.

Ltac caseb H :=
  match type of H with
  | is_true ([&& _, _ & _ ]) =>
    let H0 := fresh in
    let H1 := fresh in
    move/andP: H => [H0 H1]; caseb H1; first [caseb H0 | move: H0]
  | is_true ([&& _ & _ ]) =>
    let H0 := fresh in
    let H1 := fresh in
    move/andP: H => [H0 H1]; first [caseb H1 | move: H1]; first [caseb H0 | move: H0]
  | is_true (_ && _) =>
    let H0 := fresh in
    let H1 := fresh in
    move/andP: H => [H0 H1]; first [caseb H1 | move: H1]; first [caseb H0 | move: H0]
  | [/\ _, _, _, _ & _ ] =>
    let H0 := fresh in
    let H1 := fresh in
    move: H => [H0 H1]; first [caseb H1 | move: H1]; first [caseb H0 | move: H0]
  | [/\ _, _, _ & _ ] =>
    let H0 := fresh in
    let H1 := fresh in
    move: H => [H0 H1]; first [caseb H1 | move: H1]; first [caseb H0 | move: H0]
  | [/\ _, _ & _ ] =>
    let H0 := fresh in
    let H1 := fresh in
    move: H => [H0 H1]; first [caseb H1 | move: H1]; first [caseb H0 | move: H0]
  | [/\ _ & _ ] =>
    let H0 := fresh in
    let H1 := fresh in
    move: H => [H0 H1]; first [caseb H1 | move: H1]; first [caseb H0 | move: H0]
  | _ /\ _ =>
    let H0 := fresh in
    let H1 := fresh in
    move: H => [H0 H1]; first [caseb H1 | move: H1]; first [caseb H0 | move: H0]
  | is_true ([|| _, _ | _ ]) =>
    let H0 := fresh in
    move/orP: H; case; [idtac | move=> H0; caseb H0]
  | is_true ([|| _ | _ ]) => move/orP: H; case
  | is_true (_ || _) => move/orP: H; case
  | [\/ _, _, _ | _ ] => elim: H
  | [\/ _, _ | _ ] => elim: H
  | [\/ _ | _ ] => elim: H
  | _ \/ _ => elim: H
  end.

Ltac case_if :=
  repeat
    match goal with
    | H : context f [if ?e then _ else _] |- _ =>
        repeat match goal with
               | H : context c [e] |- _ => move: H
               end;
        (dcase e); case; intros
    | |- context f [if ?e then _ else _] =>
        repeat match goal with
               | H : context c [e] |- _ => move: H
               end;
        dcase e; case; intros
    end.

Ltac applyb H :=
  match goal with
  | H: is_true (negb _) |- False => apply: (negP H) => H
  | H: is_true (negb _) |- is_true (negb _) =>
    let H0 := fresh in
    apply/negP => H0; apply: (negP H); move: H0
  end.

Ltac iffb_tac :=
  match goal with
  | H : is_true ?b1 <-> is_true ?b2 |-
      is_true (~~ ?b1) <-> is_true (~~ ?b2) =>
      let H1 := fresh in
      let H2 := fresh in
      let Hs := fresh in
      let He := fresh in
      (move: H => [H1 H2]); (split=> He);
      [ apply/negP=> Hs; apply/idP: He; exact: (H2 Hs)
      | apply/negP=> Hs; apply/idP: He; exact: (H1 Hs) ]
  | H1 : is_true ?b11 <-> is_true ?b12, H2 : is_true ?b21 <-> is_true ?b22 |-
      is_true (?b11 && ?b21) <-> is_true (?b12 && ?b22) =>
      let H1a := fresh in
      let H1b := fresh in
      let H2a := fresh in
      let H2b := fresh in
      let He1 := fresh in
      let He2 := fresh in
      (move: H1 H2 => [H1a H1b] [H2a H2b]); (split => /andP [He1 He2]);
      [ by rewrite (H1a He1) (H2a He2)
      | by rewrite (H1b He1) (H2b He2) ]
  | H1 : is_true (?b11) <-> is_true ?b12, H2 : is_true ?b21 <-> is_true ?b22 |-
      is_true (?b11 || ?b21) <-> is_true (?b12 || ?b22) =>
      let H1a := fresh in
      let H1b := fresh in
      let H2a := fresh in
      let H2b := fresh in
      let He := fresh in
      (move: H1 H2 => [H1a H1b] [H2a H2b]); (split => /orP [] He);
      [ by rewrite (H1a He)
      | by rewrite (H2a He) orbT
      | by rewrite (H1b He)
      | by rewrite (H2b He) orbT ]
  end.


Ltac sethave e1 e2 := set e1 := e2; have: e1 = e2 by reflexivity.

Ltac caseb_hyps :=
  repeat (match goal with
          | H : is_true [&& _ & _] |- _ => case/andP: H; intros
          | H : is_true [|| _ | _] |- _ => case/orP: H; intros
          end).

Ltac case_hyps :=
  repeat (match goal with
          | H : _ /\ _ |- _ => case: H; intros
          | H : _ \/ _ |- _ => case: H; intros
          | H : is_true [&& _ & _] |- _ => case/andP: H; intros
          | H : is_true [|| _ | _] |- _ => case/orP: H; intros
          end).

Ltac case_all :=
  repeat match goal with
         | |- _ -> _ => intros
         | |- _ <-> _ => split
         | |- _ /\ _ => split
         | |- is_true (_ || _) => apply/orP
         | |- _ || _ = true => apply/orP
         | |- is_true (_ && _) => apply/andP
         | |- _ && _ = true => apply/andP
         | H : _ /\ _ |- _ => let H1 := fresh in
                              let H2 := fresh in
                              case: H => H1 H2
         | H : _ && _ |- _ => move/andP: H => H
         | H : is_true (_ && _) |- _ => move/andP: H => H
         | H : _ && _ = true |- _ => move/andP: H => H
         | H : _ \/ _ |- _ => case: H => H
         | H : is_true (_ || _) |- _ => move/orP: H => H
         | H : _ || _ = true |- _ => move/orP: H => H
         | |- context [~~ ~~ _] => rewrite negb_involutive
         | H : context [~~ ~~ _] |- _ => rewrite negb_involutive in H
         | |- context [~~ (_ && _)] => rewrite negb_andb
         | H : context [~~ (_ && _)] |- _ => rewrite negb_andb in H
         | |- context [~~ (_ || _)] => rewrite negb_orb
         | H : context [~~ (_ || _)] |- _ => rewrite negb_orb in H
         | |- _ && _ = false => apply/andb_false_iff
         | H : _ && _ = false |- _ => move/andb_false_iff: H => H
         | |- _ || _ = false => apply/orb_false_iff
         | H : _ || _ = false |- _ => move/orb_false_iff: H => H
         end.

Ltac t_decide_hook := fail.

(* Decide the goal *)
Ltac t_decide :=
  repeat (match goal with
          | H : is_true false |- _ => discriminate
          | |- is_true true => reflexivity
          | |- ?e = ?e => reflexivity
          | H : ?e |- ?e => assumption
          | |- _ /\ _ => split
          | H : ?e |- context [?e || _] => rewrite H orTb
          | H : ?e |- context [_ || ?e] => rewrite H orbT
          | H : ?e |- context [?e && _] => rewrite H andTb
          | H : ?e |- context [_ && ?e] => rewrite H andbT
          | |- context [?e == ?e] => rewrite eqxx
          | |- context [_ || true] => rewrite orbT
          | |- context [true || _] => rewrite orTb
          | |- context [_ && true] => rewrite andbT
          | |- context [true && _] => rewrite andTb
          | |- context [_ || false] => rewrite orbF
          | |- context [false || _] => rewrite orFb
          | |- context [_ && false] => rewrite andbF
          | |- context [false && _] => rewrite andFb
          | |- _ => t_decide_hook
          end).

(* Clear some useless hypotheses *)
Ltac t_clear :=
  repeat (match goal with
          | H : is_true true |- _ => clear H
          | H : ?e = ?e |- _ => clear H
          | H : is_true (?e == ?e) |- _ => clear H
          | H : context [_ || true] |- _ => rewrite orbT in H
          | H : context [true || _] |- _ => rewrite orTb in H
          | H : context [_ || false] |- _ => rewrite orbF in H
          | H : context [false || _] |- _ => rewrite orFb in H
          | H : context [_ && true] |- _ => rewrite andbT in H
          | H : context [true && _] |- _ => rewrite andTb in H
          | H : context [_ && false] |- _ => rewrite andbF in H
          | H : context [false && _] |- _ => rewrite andFb in H
          end).

(* Substitute using all equalities *)
Ltac subst_all :=
  repeat (match goal with
          | H : ?e = ?e |- _ => clear H
          | H : is_true (?e == ?e) |- _ => clear H
          | H : is_true (_ == _) |- _ => move/eqP: H; intro H
          | H1 : is_true ?e, H2 : context [?e] |- _ => rewrite H1 in H2
          | H : is_true ?e |- context [?e] => rewrite H
          | H1 : ?e = _, H2 : context [?e] |- _ => rewrite H1 in H2
          | H : ?e = _ |- _ => try rewrite H; first [injection H; intros | clear H]
          | H1 : _ = ?e, H2 : context [?e] |- _ => rewrite -H1 in H2
          | H : _ = ?e |- _ => try rewrite -H; first [injection H; intros | clear H]
          end).

Ltac t_auto_first := idtac.
Ltac t_auto_hook := fail.

Ltac t_auto_first_with f t :=
  (f unit); intros;
  repeat (case_hyps; t_clear || subst_all || iffb_tac || t_decide || (t unit)).

Ltac t_auto_with t := t_auto_first_with ltac:(fun _ => t_auto_first) t.

Tactic Notation "t_auto" :=
  t_auto_first_with ltac:(fun _ => t_auto_first) ltac:(fun _ => t_auto_hook).
Tactic Notation "t_auto" "with" tactic(t) :=
  t_auto_first_with ltac:(fun _ => t_auto_first) ltac:(t).
Tactic Notation "t_auto" "first" tactic(f) "with" tactic(t) :=
  t_auto_first_with ltac:(f) ltac:(t).
