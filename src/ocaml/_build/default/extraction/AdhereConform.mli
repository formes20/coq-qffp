open State
open Eqtype
open Seq
open Ssrnat

val conform_exp : QFBV.QFBV.exp -> SSAStore.t -> TypEnv.SSATE.env -> bool

val conform_bexp : QFBV.QFBV.bexp -> SSAStore.t -> TypEnv.SSATE.env -> bool
