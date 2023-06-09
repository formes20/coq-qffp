(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(declare-fun x9_2 () (_ BitVec 64))
(declare-fun x8_2 () (_ BitVec 64))
(declare-fun x5_2 () (_ BitVec 64))
(declare-fun x4_2 () (_ BitVec 64))
(declare-fun x3_2 () (_ BitVec 64))
(declare-fun x3_1 () (_ BitVec 64))
(declare-fun x2_2 () (_ BitVec 64))
(declare-fun x15_1 () (_ BitVec 64))
(declare-fun x14_1 () (_ BitVec 64))
(declare-fun x13_1 () (_ BitVec 64))
(declare-fun x12_1 () (_ BitVec 64))
(declare-fun x11_2 () (_ BitVec 64))
(declare-fun x10_2 () (_ BitVec 64))
(declare-fun neqz_1 () (_ BitVec 1))
(declare-fun m3_0 () (_ BitVec 64))
(declare-fun m2_0 () (_ BitVec 64))
(declare-fun m1_0 () (_ BitVec 64))
(declare-fun m0_0 () (_ BitVec 64))
(declare-fun flag_0 () (_ BitVec 64))
(declare-fun eqz_1 () (_ BitVec 1))
(declare-fun dontcare_3 () (_ BitVec 64))
(declare-fun dontcare_2 () (_ BitVec 64))
(declare-fun dontcare_1 () (_ BitVec 1))
(declare-fun carry_3 () (_ BitVec 1))
(declare-fun carry_2 () (_ BitVec 1))
(declare-fun carry_1 () (_ BitVec 1))
(declare-fun a3_0 () (_ BitVec 64))
(declare-fun a2_0 () (_ BitVec 64))
(declare-fun a1_0 () (_ BitVec 64))
(declare-fun a0_0 () (_ BitVec 64))
(assert (and (and (and (and (= m0_0 #xFFFFFFFF00000001) (= m1_0 #x53BDA402FFFE5BFE)) (= m2_0 #x3339D80809A1D805)) (= m3_0 #x73EDA753299D7D48)) (bvult (bvadd (bvmul ((_ zero_extend 192) a0_0) #x0000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 192) a1_0) #x0000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 192) a2_0) #x0000000000000000000000000000000100000000000000000000000000000000) (bvmul ((_ zero_extend 192) a3_0) #x0000000000000001000000000000000000000000000000000000000000000000)))) (bvadd (bvmul ((_ zero_extend 192) m0_0) #x0000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 192) m1_0) #x0000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 192) m2_0) #x0000000000000000000000000000000100000000000000000000000000000000) (bvmul ((_ zero_extend 192) m3_0) #x0000000000000001000000000000000000000000000000000000000000000000)))))))
(assert (and (= carry_1 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) m0_0) ((_ zero_extend 1) (bvnot a0_0))) #b00000000000000000000000000000000000000000000000000000000000000001))) (= x12_1 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) m0_0) ((_ zero_extend 1) (bvnot a0_0))) #b00000000000000000000000000000000000000000000000000000000000000001)))))
(assert (= x4_2 (bvor a0_0 a1_0)))
(assert (and (= carry_2 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) m1_0) ((_ zero_extend 1) (bvnot a1_0))) ((_ zero_extend 64) carry_1)))) (= x13_1 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) m1_0) ((_ zero_extend 1) (bvnot a1_0))) ((_ zero_extend 64) carry_1))))))
(assert (= x5_2 (bvor a2_0 a3_0)))
(assert (and (= carry_3 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) m2_0) ((_ zero_extend 1) (bvnot a2_0))) ((_ zero_extend 64) carry_2)))) (= x14_1 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) m2_0) ((_ zero_extend 1) (bvnot a2_0))) ((_ zero_extend 64) carry_2))))))
(assert (= x3_1 (bvor x4_2 x5_2)))
(assert (and (= dontcare_1 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) m3_0) ((_ zero_extend 1) (bvnot a3_0))) ((_ zero_extend 64) carry_3)))) (= x15_1 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) m3_0) ((_ zero_extend 1) (bvnot a3_0))) ((_ zero_extend 64) carry_3))))))
(assert (and (= neqz_1 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) x3_1) ((_ zero_extend 1) (bvnot #x0000000000000001))) #b00000000000000000000000000000000000000000000000000000000000000001))) (= dontcare_2 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) x3_1) ((_ zero_extend 1) (bvnot #x0000000000000001))) #b00000000000000000000000000000000000000000000000000000000000000001)))))
(assert (= x3_2 (ite (= neqz_1 #b1) #xFFFFFFFFFFFFFFFF #x0000000000000000)))
(assert (= x2_2 (bvand flag_0 x3_2)))
(assert (and (= eqz_1 ((_ extract 64 64) (bvsub ((_ zero_extend 1) x2_2) ((_ zero_extend 1) #x0000000000000001)))) (= dontcare_3 ((_ extract 63 0) (bvsub ((_ zero_extend 1) x2_2) ((_ zero_extend 1) #x0000000000000001))))))
(assert (= x8_2 (ite (= eqz_1 #b1) a0_0 x12_1)))
(assert (= x9_2 (ite (= eqz_1 #b1) a1_0 x13_1)))
(assert (= x10_2 (ite (= eqz_1 #b1) a2_0 x14_1)))
(assert (= x11_2 (ite (= eqz_1 #b1) a3_0 x15_1)))
(assert (not (or (and (= flag_0 #x0000000000000000) (= (bvurem (bvadd (bvmul ((_ zero_extend 192) x8_2) #x0000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 192) x9_2) #x0000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 192) x10_2) #x0000000000000000000000000000000100000000000000000000000000000000) (bvmul ((_ zero_extend 192) x11_2) #x0000000000000001000000000000000000000000000000000000000000000000)))) (bvadd (bvmul ((_ zero_extend 192) m0_0) #x0000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 192) m1_0) #x0000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 192) m2_0) #x0000000000000000000000000000000100000000000000000000000000000000) (bvmul ((_ zero_extend 192) m3_0) #x0000000000000001000000000000000000000000000000000000000000000000))))) (bvurem (bvadd (bvmul ((_ zero_extend 192) a0_0) #x0000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 192) a1_0) #x0000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 192) a2_0) #x0000000000000000000000000000000100000000000000000000000000000000) (bvmul ((_ zero_extend 192) a3_0) #x0000000000000001000000000000000000000000000000000000000000000000)))) (bvadd (bvmul ((_ zero_extend 192) m0_0) #x0000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 192) m1_0) #x0000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 192) m2_0) #x0000000000000000000000000000000100000000000000000000000000000000) (bvmul ((_ zero_extend 192) m3_0) #x0000000000000001000000000000000000000000000000000000000000000000))))))) (and (bvugt flag_0 #x0000000000000000) (= (bvurem (bvadd (bvadd (bvmul ((_ zero_extend 192) x8_2) #x0000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 192) x9_2) #x0000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 192) x10_2) #x0000000000000000000000000000000100000000000000000000000000000000) (bvmul ((_ zero_extend 192) x11_2) #x0000000000000001000000000000000000000000000000000000000000000000)))) (bvadd (bvmul ((_ zero_extend 192) a0_0) #x0000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 192) a1_0) #x0000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 192) a2_0) #x0000000000000000000000000000000100000000000000000000000000000000) (bvmul ((_ zero_extend 192) a3_0) #x0000000000000001000000000000000000000000000000000000000000000000))))) (bvadd (bvmul ((_ zero_extend 192) m0_0) #x0000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 192) m1_0) #x0000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 192) m2_0) #x0000000000000000000000000000000100000000000000000000000000000000) (bvmul ((_ zero_extend 192) m3_0) #x0000000000000001000000000000000000000000000000000000000000000000))))) (bvurem #x0000000000000000000000000000000000000000000000000000000000000000 (bvadd (bvmul ((_ zero_extend 192) m0_0) #x0000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 192) m1_0) #x0000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 192) m2_0) #x0000000000000000000000000000000100000000000000000000000000000000) (bvmul ((_ zero_extend 192) m3_0) #x0000000000000001000000000000000000000000000000000000000000000000))))))))))
(check-sat)
(exit)
