(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(declare-fun rsi_2 () (_ BitVec 64))
(declare-fun rdx_2 () (_ BitVec 64))
(declare-fun rcx_2 () (_ BitVec 64))
(declare-fun rax_3 () (_ BitVec 64))
(declare-fun r9_3 () (_ BitVec 64))
(declare-fun r9_2 () (_ BitVec 64))
(declare-fun r8_3 () (_ BitVec 64))
(declare-fun r8_2 () (_ BitVec 64))
(declare-fun r11_3 () (_ BitVec 64))
(declare-fun r11_2 () (_ BitVec 64))
(declare-fun r10_3 () (_ BitVec 64))
(declare-fun r10_2 () (_ BitVec 64))
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
(assert (and (bvult (bvadd (bvmul ((_ zero_extend 192) a0_0) #x0000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 192) a1_0) #x0000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 192) a2_0) #x0000000000000000000000000000000100000000000000000000000000000000) (bvmul ((_ zero_extend 192) a3_0) #x0000000000000001000000000000000000000000000000000000000000000000)))) (bvadd (bvmul ((_ zero_extend 192) #xA700000000000013) #x0000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 192) #x6121000000000013) #x0000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 192) #xBA344D8000000008) #x0000000000000000000000000000000100000000000000000000000000000000) (bvmul ((_ zero_extend 192) #x2523648240000001) #x0000000000000001000000000000000000000000000000000000000000000000))))) (bvult (bvadd (bvmul ((_ zero_extend 192) b0_0) #x0000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 192) b1_0) #x0000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 192) b2_0) #x0000000000000000000000000000000100000000000000000000000000000000) (bvmul ((_ zero_extend 192) b3_0) #x0000000000000001000000000000000000000000000000000000000000000000)))) (bvadd (bvmul ((_ zero_extend 192) #xA700000000000013) #x0000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 192) #x6121000000000013) #x0000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 192) #xBA344D8000000008) #x0000000000000000000000000000000100000000000000000000000000000000) (bvmul ((_ zero_extend 192) #x2523648240000001) #x0000000000000001000000000000000000000000000000000000000000000000)))))))
(assert (and (= carry_1 ((_ extract 64 64) (bvadd ((_ zero_extend 1) b0_0) ((_ zero_extend 1) a0_0)))) (= r8_2 ((_ extract 63 0) (bvadd ((_ zero_extend 1) b0_0) ((_ zero_extend 1) a0_0))))))
(assert (and (= carry_2 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) b1_0) ((_ zero_extend 1) a1_0)) ((_ zero_extend 64) carry_1)))) (= r9_2 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) b1_0) ((_ zero_extend 1) a1_0)) ((_ zero_extend 64) carry_1))))))
(assert (and (= carry_3 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) b2_0) ((_ zero_extend 1) a2_0)) ((_ zero_extend 64) carry_2)))) (= r10_2 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) b2_0) ((_ zero_extend 1) a2_0)) ((_ zero_extend 64) carry_2))))))
(assert (and (= carry_4 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) b3_0) ((_ zero_extend 1) a3_0)) ((_ zero_extend 64) carry_3)))) (= r11_2 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) b3_0) ((_ zero_extend 1) a3_0)) ((_ zero_extend 64) carry_3))))))
(assert (and (= carry_5 ((_ extract 64 64) (bvsub ((_ zero_extend 1) r8_2) ((_ zero_extend 1) #xA700000000000013)))) (= rax_3 ((_ extract 63 0) (bvsub ((_ zero_extend 1) r8_2) ((_ zero_extend 1) #xA700000000000013))))))
(assert (and (= carry_6 ((_ extract 64 64) (bvsub ((_ zero_extend 1) r9_2) (bvadd ((_ zero_extend 1) #x6121000000000013) ((_ zero_extend 64) carry_5))))) (= rcx_2 ((_ extract 63 0) (bvsub ((_ zero_extend 1) r9_2) (bvadd ((_ zero_extend 1) #x6121000000000013) ((_ zero_extend 64) carry_5)))))))
(assert (and (= carry_7 ((_ extract 64 64) (bvsub ((_ zero_extend 1) r10_2) (bvadd ((_ zero_extend 1) #xBA344D8000000008) ((_ zero_extend 64) carry_6))))) (= rdx_2 ((_ extract 63 0) (bvsub ((_ zero_extend 1) r10_2) (bvadd ((_ zero_extend 1) #xBA344D8000000008) ((_ zero_extend 64) carry_6)))))))
(assert (and (= carry_8 ((_ extract 64 64) (bvsub ((_ zero_extend 1) r11_2) (bvadd ((_ zero_extend 1) #x2523648240000001) ((_ zero_extend 64) carry_7))))) (= rsi_2 ((_ extract 63 0) (bvsub ((_ zero_extend 1) r11_2) (bvadd ((_ zero_extend 1) #x2523648240000001) ((_ zero_extend 64) carry_7)))))))
(assert (= r8_3 (ite (= carry_8 #b1) r8_2 rax_3)))
(assert (= r9_3 (ite (= carry_8 #b1) r9_2 rcx_2)))
(assert (= r10_3 (ite (= carry_8 #b1) r10_2 rdx_2)))
(assert (= r11_3 (ite (= carry_8 #b1) r11_2 rsi_2)))
(assert (not (= (bvurem (bvadd (bvmul ((_ zero_extend 192) r8_3) #x0000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 192) r9_3) #x0000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 192) r10_3) #x0000000000000000000000000000000100000000000000000000000000000000) (bvmul ((_ zero_extend 192) r11_3) #x0000000000000001000000000000000000000000000000000000000000000000)))) (bvadd (bvmul ((_ zero_extend 192) #xA700000000000013) #x0000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 192) #x6121000000000013) #x0000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 192) #xBA344D8000000008) #x0000000000000000000000000000000100000000000000000000000000000000) (bvmul ((_ zero_extend 192) #x2523648240000001) #x0000000000000001000000000000000000000000000000000000000000000000))))) (bvurem (bvadd (bvadd (bvmul ((_ zero_extend 192) a0_0) #x0000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 192) a1_0) #x0000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 192) a2_0) #x0000000000000000000000000000000100000000000000000000000000000000) (bvmul ((_ zero_extend 192) a3_0) #x0000000000000001000000000000000000000000000000000000000000000000)))) (bvadd (bvmul ((_ zero_extend 192) b0_0) #x0000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 192) b1_0) #x0000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 192) b2_0) #x0000000000000000000000000000000100000000000000000000000000000000) (bvmul ((_ zero_extend 192) b3_0) #x0000000000000001000000000000000000000000000000000000000000000000))))) (bvadd (bvmul ((_ zero_extend 192) #xA700000000000013) #x0000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 192) #x6121000000000013) #x0000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 192) #xBA344D8000000008) #x0000000000000000000000000000000100000000000000000000000000000000) (bvmul ((_ zero_extend 192) #x2523648240000001) #x0000000000000001000000000000000000000000000000000000000000000000))))))))
(check-sat)
(exit)
