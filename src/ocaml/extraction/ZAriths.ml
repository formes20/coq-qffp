open BinInt
open BinNat
open BinNums
open BinPos
open Bool
open Eqtype

let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val pos_eqP : positive -> positive -> reflect **)

let pos_eqP n m =
  let _evar_0_ = fun _ -> ReflectT in
  let _evar_0_0 = fun _ -> ReflectF in
  if Pos.eqb n m then _evar_0_ __ else _evar_0_0 __

(** val pos_eqMixin : positive Equality.mixin_of **)

let pos_eqMixin =
  { Equality.op = Pos.eqb; Equality.mixin_of__1 = pos_eqP }

(** val pos_eqType : Equality.coq_type **)

let pos_eqType =
  Obj.magic pos_eqMixin

(** val coq_N_eqP : coq_N -> coq_N -> reflect **)

let coq_N_eqP n m =
  let _evar_0_ = fun _ -> ReflectT in
  let _evar_0_0 = fun _ -> ReflectF in
  if N.eqb n m then _evar_0_ __ else _evar_0_0 __

(** val coq_N_eqMixin : coq_N Equality.mixin_of **)

let coq_N_eqMixin =
  { Equality.op = N.eqb; Equality.mixin_of__1 = coq_N_eqP }

(** val coq_N_eqType : Equality.coq_type **)

let coq_N_eqType =
  Obj.magic coq_N_eqMixin

(** val coq_Z_eqP : coq_Z -> coq_Z -> reflect **)

let coq_Z_eqP n m =
  let _evar_0_ = fun _ -> ReflectT in
  let _evar_0_0 = fun _ -> ReflectF in
  if Z.eqb n m then _evar_0_ __ else _evar_0_0 __

(** val coq_Z_eqMixin : coq_Z Equality.mixin_of **)

let coq_Z_eqMixin =
  { Equality.op = Z.eqb; Equality.mixin_of__1 = coq_Z_eqP }

(** val coq_Z_eqType : Equality.coq_type **)

let coq_Z_eqType =
  Obj.magic coq_Z_eqMixin
