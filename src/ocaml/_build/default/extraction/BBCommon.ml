open BinNums
open BinPos
open CNF
open EqVar
open NBitsOp

(** val cnf_lit_eq : literal -> literal -> literal list list **)

let cnf_lit_eq a1 a2 =
  ((neg_lit a1) :: (a2 :: [])) :: ((a1 :: ((neg_lit a2) :: [])) :: [])

(** val extzip_ff :
    literal list -> literal list -> (literal * literal) list **)

let extzip_ff =
  extzip lit_ff lit_ff

type generator = positive

(** val gen : generator -> generator * literal **)

let gen g =
  ((Pos.add g Coq_xH), (Pos g))

type vm = word SSAVM.t
