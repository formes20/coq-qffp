(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(declare-fun x9_2 () (_ BitVec 64))
(declare-fun x8_2 () (_ BitVec 64))
(declare-fun x17_3 () (_ BitVec 64))
(declare-fun x17_2 () (_ BitVec 64))
(declare-fun x16_3 () (_ BitVec 64))
(declare-fun x16_2 () (_ BitVec 64))
(declare-fun x15_3 () (_ BitVec 64))
(declare-fun x15_2 () (_ BitVec 64))
(declare-fun x14_3 () (_ BitVec 64))
(declare-fun x14_2 () (_ BitVec 64))
(declare-fun x11_2 () (_ BitVec 64))
(declare-fun x10_2 () (_ BitVec 64))
(declare-fun x1_1 () (_ BitVec 64))
(declare-fun dontcare_1 () (_ BitVec 64))
(declare-fun carry_9 () (_ BitVec 1))
(declare-fun carry_8 () (_ BitVec 1))
(declare-fun carry_7 () (_ BitVec 1))
(declare-fun carry_6 () (_ BitVec 1))
(declare-fun carry_5 () (_ BitVec 1))
(declare-fun carry_4 () (_ BitVec 1))
(declare-fun carry_3 () (_ BitVec 1))
(declare-fun carry_2 () (_ BitVec 1))
(declare-fun carry_1 () (_ BitVec 1))
(declare-fun b3_0 () (_ BitVec 64))
(declare-fun b2_0 () (_ BitVec 64))
(declare-fun b1_0 () (_ BitVec 64))
(declare-fun b0_0 () (_ BitVec 64))
(declare-fun a3_0 () (_ BitVec 64))
(declare-fun a2_0 () (_ BitVec 64))
(declare-fun a1_0 () (_ BitVec 64))
(declare-fun a0_0 () (_ BitVec 64))
(assert (and (bvult (bvadd (bvmul ((_ zero_extend 192) a0_0) #x0000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 192) a1_0) #x0000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 192) a2_0) #x0000000000000000000000000000000100000000000000000000000000000000) (bvmul ((_ zero_extend 192) a3_0) #x0000000000000001000000000000000000000000000000000000000000000000)))) (bvadd (bvmul ((_ zero_extend 192) #xFFFFFFFFFFFFFFFF) #x0000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 192) #x00000000FFFFFFFF) #x0000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 192) #x0000000000000000) #x0000000000000000000000000000000100000000000000000000000000000000) (bvmul ((_ zero_extend 192) #xFFFFFFFF00000001) #x0000000000000001000000000000000000000000000000000000000000000000))))) (bvult (bvadd (bvmul ((_ zero_extend 192) b0_0) #x0000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 192) b1_0) #x0000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 192) b2_0) #x0000000000000000000000000000000100000000000000000000000000000000) (bvmul ((_ zero_extend 192) b3_0) #x0000000000000001000000000000000000000000000000000000000000000000)))) (bvadd (bvmul ((_ zero_extend 192) #xFFFFFFFFFFFFFFFF) #x0000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 192) #x00000000FFFFFFFF) #x0000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 192) #x0000000000000000) #x0000000000000000000000000000000100000000000000000000000000000000) (bvmul ((_ zero_extend 192) #xFFFFFFFF00000001) #x0000000000000001000000000000000000000000000000000000000000000000)))))))
(assert (and (= carry_1 ((_ extract 64 64) (bvadd ((_ zero_extend 1) a0_0) ((_ zero_extend 1) b0_0)))) (= x14_2 ((_ extract 63 0) (bvadd ((_ zero_extend 1) a0_0) ((_ zero_extend 1) b0_0))))))
(assert (and (= carry_2 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) a1_0) ((_ zero_extend 1) b1_0)) ((_ zero_extend 64) carry_1)))) (= x15_2 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) a1_0) ((_ zero_extend 1) b1_0)) ((_ zero_extend 64) carry_1))))))
(assert (and (= carry_3 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) a2_0) ((_ zero_extend 1) b2_0)) ((_ zero_extend 64) carry_2)))) (= x16_2 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) a2_0) ((_ zero_extend 1) b2_0)) ((_ zero_extend 64) carry_2))))))
(assert (and (= carry_4 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) a3_0) ((_ zero_extend 1) b3_0)) ((_ zero_extend 64) carry_3)))) (= x17_2 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) a3_0) ((_ zero_extend 1) b3_0)) ((_ zero_extend 64) carry_3))))))
(assert (= x1_1 (bvadd (bvadd #x0000000000000000 #x0000000000000000) ((_ zero_extend 63) carry_4))))
(assert true)
(assert (and (= carry_5 ((_ extract 64 64) (bvadd ((_ zero_extend 1) x14_2) ((_ zero_extend 1) #x0000000000000001)))) (= x8_2 ((_ extract 63 0) (bvadd ((_ zero_extend 1) x14_2) ((_ zero_extend 1) #x0000000000000001))))))
(assert true)
(assert (and (= carry_6 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) x15_2) ((_ zero_extend 1) (bvnot #x00000000FFFFFFFF))) ((_ zero_extend 64) carry_5)))) (= x9_2 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) x15_2) ((_ zero_extend 1) (bvnot #x00000000FFFFFFFF))) ((_ zero_extend 64) carry_5))))))
(assert (and (= carry_7 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) x16_2) ((_ zero_extend 1) (bvnot #x0000000000000000))) ((_ zero_extend 64) carry_6)))) (= x10_2 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) x16_2) ((_ zero_extend 1) (bvnot #x0000000000000000))) ((_ zero_extend 64) carry_6))))))
(assert (and (= carry_8 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) x17_2) ((_ zero_extend 1) (bvnot #xFFFFFFFF00000001))) ((_ zero_extend 64) carry_7)))) (= x11_2 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) x17_2) ((_ zero_extend 1) (bvnot #xFFFFFFFF00000001))) ((_ zero_extend 64) carry_7))))))
(assert (and (= carry_9 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) x1_1) ((_ zero_extend 1) (bvnot #x0000000000000000))) ((_ zero_extend 64) carry_8)))) (= dontcare_1 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) x1_1) ((_ zero_extend 1) (bvnot #x0000000000000000))) ((_ zero_extend 64) carry_8))))))
(assert (= x14_3 (ite (= carry_9 #b1) x8_2 x14_2)))
(assert (= x15_3 (ite (= carry_9 #b1) x9_2 x15_2)))
(assert (= x16_3 (ite (= carry_9 #b1) x10_2 x16_2)))
(assert (= x17_3 (ite (= carry_9 #b1) x11_2 x17_2)))
(assert (not (= (bvurem (bvadd (bvadd (bvmul ((_ zero_extend 256) a0_0) #x00000000000000000000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 256) a1_0) #x00000000000000000000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 256) a2_0) #x00000000000000000000000000000000000000000000000100000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 256) a3_0) #x00000000000000000000000000000001000000000000000000000000000000000000000000000000) (bvmul ((_ zero_extend 256) #x0000000000000000) #x00000000000000010000000000000000000000000000000000000000000000000000000000000000))))) (bvadd (bvmul ((_ zero_extend 256) b0_0) #x00000000000000000000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 256) b1_0) #x00000000000000000000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 256) b2_0) #x00000000000000000000000000000000000000000000000100000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 256) b3_0) #x00000000000000000000000000000001000000000000000000000000000000000000000000000000) (bvmul ((_ zero_extend 256) #x0000000000000000) #x00000000000000010000000000000000000000000000000000000000000000000000000000000000)))))) (bvadd (bvmul ((_ zero_extend 256) #xFFFFFFFFFFFFFFFF) #x00000000000000000000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 256) #x00000000FFFFFFFF) #x00000000000000000000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 256) #x0000000000000000) #x00000000000000000000000000000000000000000000000100000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 256) #xFFFFFFFF00000001) #x00000000000000000000000000000001000000000000000000000000000000000000000000000000) (bvmul ((_ zero_extend 256) #x0000000000000000) #x00000000000000010000000000000000000000000000000000000000000000000000000000000000)))))) (bvurem (bvadd (bvmul ((_ zero_extend 256) x14_3) #x00000000000000000000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 256) x15_3) #x00000000000000000000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 256) x16_3) #x00000000000000000000000000000000000000000000000100000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 256) x17_3) #x00000000000000000000000000000001000000000000000000000000000000000000000000000000) (bvmul ((_ zero_extend 256) #x0000000000000000) #x00000000000000010000000000000000000000000000000000000000000000000000000000000000))))) (bvadd (bvmul ((_ zero_extend 256) #xFFFFFFFFFFFFFFFF) #x00000000000000000000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 256) #x00000000FFFFFFFF) #x00000000000000000000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 256) #x0000000000000000) #x00000000000000000000000000000000000000000000000100000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 256) #xFFFFFFFF00000001) #x00000000000000000000000000000001000000000000000000000000000000000000000000000000) (bvmul ((_ zero_extend 256) #x0000000000000000) #x00000000000000010000000000000000000000000000000000000000000000000000000000000000)))))))))
(check-sat)
(exit)
