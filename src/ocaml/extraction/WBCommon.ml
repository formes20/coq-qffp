open EqVar
open NBitsDef
open Typ
open Seq
open Ssrnat

(** val make_exp_var :
    (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list -> TypEnv.SSATE.env
    -> QFBV.QFBV.exp -> int -> ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp
    list) * QFBV.QFBV.exp **)

let make_exp_var gen_var g es te target bs_size =
  let ty = Tuint bs_size in
  let (v, g') = gen_var g in
  let te' = TypEnv.SSATE.add v ty te in
  let var_exp = QFBV.QFBV.Evar v in
  let eq_bexp = QFBV.QFBV.Bbinop (QFBV.QFBV.Beq, var_exp, target) in
  let es' = eq_bexp :: es in (((te', g'), es'), var_exp)

(** val make_Evar :
    (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list -> TypEnv.SSATE.env
    -> int -> ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp list) * QFBV.QFBV.exp **)

let make_Evar gen_var g es te bs_size =
  let ty = Tuint bs_size in
  let (v, g') = gen_var g in
  let te' = TypEnv.SSATE.add v ty te in
  let var_exp = QFBV.QFBV.Evar v in (((te', g'), es), var_exp)

(** val make_bexp_var :
    (int -> ssavar * int) -> int -> QFBV.QFBV.bexp list -> TypEnv.SSATE.env
    -> QFBV.QFBV.bexp -> ((TypEnv.SSATE.env * int) * QFBV.QFBV.bexp
    list) * QFBV.QFBV.bexp **)

let make_bexp_var gen_var g es te target =
  let ty = Tuint (Pervasives.succ 0) in
  let (v, g') = gen_var g in
  let te' = TypEnv.SSATE.add v ty te in
  let var_exp = QFBV.QFBV.Evar v in
  let target_exp = QFBV.QFBV.Eite (target, (QFBV.QFBV.Econst (true :: [])),
    (QFBV.QFBV.Econst (false :: [])))
  in
  let eq_bexp = QFBV.QFBV.Bbinop (QFBV.QFBV.Beq, var_exp, target_exp) in
  let bs' = eq_bexp :: es in
  (((te', g'), bs'), (QFBV.QFBV.Bbinop (QFBV.QFBV.Beq, var_exp,
  (QFBV.QFBV.Econst (true :: [])))))

(** val msb_bexp : QFBV.QFBV.exp -> QFBV.QFBV.bexp **)

let msb_bexp bs =
  QFBV.QFBV.Bbinop (QFBV.QFBV.Beq, (QFBV.QFBV.Eunop ((QFBV.QFBV.Uhigh
    (Pervasives.succ 0)), bs)), (QFBV.QFBV.Econst (true :: [])))

(** val lsb_bexp : QFBV.QFBV.exp -> QFBV.QFBV.bexp **)

let lsb_bexp bs =
  QFBV.QFBV.Bbinop (QFBV.QFBV.Beq, (QFBV.QFBV.Eunop ((QFBV.QFBV.Ulow
    (Pervasives.succ 0)), bs)), (QFBV.QFBV.Econst (true :: [])))

(** val zero_exp : int -> QFBV.QFBV.exp **)

let zero_exp n =
  QFBV.QFBV.Econst (zeros n)

(** val ones_exp : int -> QFBV.QFBV.exp **)

let ones_exp n =
  QFBV.QFBV.Econst (ones n)

(** val one_exp : int -> QFBV.QFBV.exp **)

let one_exp n =
  QFBV.QFBV.Econst (cat (true :: []) (zeros (subn n (Pervasives.succ 0))))

(** val is_all_zeros : QFBV.QFBV.exp -> int -> QFBV.QFBV.bexp **)

let is_all_zeros bs bs_size =
  QFBV.QFBV.Bbinop (QFBV.QFBV.Beq, bs, (zero_exp bs_size))

(** val is_all_ones : QFBV.QFBV.exp -> int -> QFBV.QFBV.bexp **)

let is_all_ones bs bs_size =
  QFBV.QFBV.Bbinop (QFBV.QFBV.Beq, bs, (ones_exp bs_size))

(** val coq_Btrue_exp : QFBV.QFBV.exp **)

let coq_Btrue_exp =
  QFBV.QFBV.Econst (true :: [])

(** val coq_Bfalse_exp : QFBV.QFBV.exp **)

let coq_Bfalse_exp =
  QFBV.QFBV.Econst (false :: [])

(** val is_Btrue : QFBV.QFBV.exp -> QFBV.QFBV.bexp **)

let is_Btrue e =
  QFBV.QFBV.Bbinop (QFBV.QFBV.Beq, e, coq_Btrue_exp)

(** val coq_Eite_bexp :
    QFBV.QFBV.bexp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp **)

let coq_Eite_bexp cond b1 b2 =
  QFBV.QFBV.Bdisj ((QFBV.QFBV.Bconj (cond, b1)), (QFBV.QFBV.Bconj
    ((QFBV.QFBV.Blneg cond), b2)))

(** val coq_Bimp : QFBV.QFBV.bexp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp **)

let coq_Bimp b1 b2 =
  QFBV.QFBV.Bdisj ((QFBV.QFBV.Blneg b1), b2)

(** val coq_Biff : QFBV.QFBV.bexp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp **)

let coq_Biff b1 b2 =
  QFBV.QFBV.Bconj ((coq_Bimp b1 b2), (coq_Bimp b2 b1))

(** val coq_Bsucc : QFBV.QFBV.exp -> int -> QFBV.QFBV.exp * QFBV.QFBV.bexp **)

let coq_Bsucc bs bs_size =
  let succ_bs = QFBV.QFBV.Ebinop (QFBV.QFBV.Badd, bs, (one_exp bs_size)) in
  let is_ovf = QFBV.QFBV.Bbinop (QFBV.QFBV.Buaddo, bs, (one_exp bs_size)) in
  (succ_bs, is_ovf)

(** val coq_Bxor_bexp : QFBV.QFBV.bexp -> QFBV.QFBV.bexp -> QFBV.QFBV.bexp **)

let coq_Bxor_bexp b1 b2 =
  QFBV.QFBV.Bdisj ((QFBV.QFBV.Bconj ((QFBV.QFBV.Blneg b1), b2)),
    (QFBV.QFBV.Bconj (b1, (QFBV.QFBV.Blneg b2))))

(** val coq_Badc :
    QFBV.QFBV.bexp -> QFBV.QFBV.exp -> QFBV.QFBV.exp -> int -> QFBV.QFBV.exp **)

let coq_Badc c bs1 bs2 bs_size =
  let sum_bs = QFBV.QFBV.Ebinop (QFBV.QFBV.Badd, bs1, bs2) in
  let carry = QFBV.QFBV.Eite (c, (one_exp bs_size), (zero_exp bs_size)) in
  QFBV.QFBV.Ebinop (QFBV.QFBV.Badd, sum_bs, carry)

(** val s_exp : int -> int -> QFBV.QFBV.exp -> QFBV.QFBV.exp **)

let s_exp mlen elen bf =
  QFBV.QFBV.Eunop ((QFBV.QFBV.Uextr ((addn elen mlen), (addn elen mlen))), bf)

(** val e_exp : int -> int -> QFBV.QFBV.exp -> QFBV.QFBV.exp **)

let e_exp mlen elen bf =
  QFBV.QFBV.Eunop ((QFBV.QFBV.Uextr
    ((addn (subn elen (Pervasives.succ 0)) mlen), mlen)), bf)

(** val m_exp : int -> QFBV.QFBV.exp -> QFBV.QFBV.exp **)

let m_exp mlen bf =
  QFBV.QFBV.Eunop ((QFBV.QFBV.Uextr ((subn mlen (Pervasives.succ 0)), 0)), bf)
