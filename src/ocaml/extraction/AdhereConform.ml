open State
open Eqtype
open Seq
open Ssrnat

(** val conform_exp :
    QFBV.QFBV.exp -> SSAStore.t -> TypEnv.SSATE.env -> bool **)

let rec conform_exp e s te =
  match e with
  | QFBV.QFBV.Evar v ->
    eq_op nat_eqType (Obj.magic TypEnv.SSATE.vsize v te)
      (Obj.magic size (SSAStore.acc v s))
  | QFBV.QFBV.Econst _ -> true
  | QFBV.QFBV.Eunop (_, e0) -> conform_exp e0 s te
  | QFBV.QFBV.Ebinop (_, e1, e2) ->
    (&&) (conform_exp e1 s te) (conform_exp e2 s te)
  | QFBV.QFBV.Eite (b, e1, e2) ->
    (&&) ((&&) (conform_bexp b s te) (conform_exp e1 s te))
      (conform_exp e2 s te)

(** val conform_bexp :
    QFBV.QFBV.bexp -> SSAStore.t -> TypEnv.SSATE.env -> bool **)

and conform_bexp b s te =
  match b with
  | QFBV.QFBV.Bbinop (_, e1, e2) ->
    (&&) (conform_exp e1 s te) (conform_exp e2 s te)
  | QFBV.QFBV.Blneg b0 -> conform_bexp b0 s te
  | QFBV.QFBV.Bconj (b1, b2) ->
    (&&) (conform_bexp b1 s te) (conform_bexp b2 s te)
  | QFBV.QFBV.Bdisj (b1, b2) ->
    (&&) (conform_bexp b1 s te) (conform_bexp b2 s te)
  | _ -> true
