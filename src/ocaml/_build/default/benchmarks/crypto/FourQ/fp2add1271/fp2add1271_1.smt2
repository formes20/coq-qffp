(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(declare-fun tmp_2 () (_ BitVec 64))
(declare-fun tmp_1 () (_ BitVec 64))
(declare-fun rsi_2 () (_ BitVec 64))
(declare-fun rdx_6 () (_ BitVec 64))
(declare-fun rdx_3 () (_ BitVec 64))
(declare-fun rdx_2 () (_ BitVec 64))
(declare-fun rdi_2 () (_ BitVec 64))
(declare-fun rax_9 () (_ BitVec 64))
(declare-fun rax_8 () (_ BitVec 64))
(declare-fun rax_5 () (_ BitVec 64))
(declare-fun rax_3 () (_ BitVec 64))
(declare-fun rax_2 () (_ BitVec 64))
(declare-fun r8_2 () (_ BitVec 64))
(declare-fun r11_2 () (_ BitVec 64))
(declare-fun carry2_2 () (_ BitVec 1))
(declare-fun carry2_1 () (_ BitVec 1))
(declare-fun carry_8 () (_ BitVec 64))
(declare-fun carry_7 () (_ BitVec 1))
(declare-fun carry_6 () (_ BitVec 1))
(declare-fun carry_5 () (_ BitVec 1))
(declare-fun carry_4 () (_ BitVec 64))
(declare-fun carry_3 () (_ BitVec 1))
(declare-fun carry_2 () (_ BitVec 1))
(declare-fun carry_1 () (_ BitVec 1))
(declare-fun L0x7fffffffe368_0 () (_ BitVec 64))
(declare-fun L0x7fffffffe360_0 () (_ BitVec 64))
(declare-fun L0x7fffffffe358_0 () (_ BitVec 64))
(declare-fun L0x7fffffffe350_0 () (_ BitVec 64))
(declare-fun L0x7fffffffe348_0 () (_ BitVec 64))
(declare-fun L0x7fffffffe340_0 () (_ BitVec 64))
(declare-fun L0x7fffffffe338_0 () (_ BitVec 64))
(declare-fun L0x7fffffffe330_0 () (_ BitVec 64))
(assert (and (and (and (bvult (bvadd (bvmul ((_ zero_extend 64) L0x7fffffffe330_0) #x00000000000000000000000000000001) (bvmul ((_ zero_extend 64) L0x7fffffffe338_0) #x00000000000000010000000000000000)) #x80000000000000000000000000000000) (bvult (bvadd (bvmul ((_ zero_extend 64) L0x7fffffffe340_0) #x00000000000000000000000000000001) (bvmul ((_ zero_extend 64) L0x7fffffffe348_0) #x00000000000000010000000000000000)) #x80000000000000000000000000000000)) (bvult (bvadd (bvmul ((_ zero_extend 64) L0x7fffffffe350_0) #x00000000000000000000000000000001) (bvmul ((_ zero_extend 64) L0x7fffffffe358_0) #x00000000000000010000000000000000)) #x80000000000000000000000000000000)) (bvult (bvadd (bvmul ((_ zero_extend 64) L0x7fffffffe360_0) #x00000000000000000000000000000001) (bvmul ((_ zero_extend 64) L0x7fffffffe368_0) #x00000000000000010000000000000000)) #x80000000000000000000000000000000)))
(assert (and (= carry_1 ((_ extract 64 64) (bvadd ((_ zero_extend 1) L0x7fffffffe350_0) ((_ zero_extend 1) L0x7fffffffe330_0)))) (= rax_2 ((_ extract 63 0) (bvadd ((_ zero_extend 1) L0x7fffffffe350_0) ((_ zero_extend 1) L0x7fffffffe330_0))))))
(assert (and (= carry_2 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) L0x7fffffffe358_0) ((_ zero_extend 1) L0x7fffffffe338_0)) ((_ zero_extend 64) carry_1)))) (= rdx_2 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) L0x7fffffffe358_0) ((_ zero_extend 1) L0x7fffffffe338_0)) ((_ zero_extend 64) carry_1))))))
(assert true)
(assert true)
(assert (and (= r11_2 ((_ zero_extend 63) ((_ extract 63 63) rdx_2))) (= tmp_1 ((_ zero_extend 1) ((_ extract 62 0) rdx_2)))))
(assert (and (= carry_3 ((_ extract 64 64) (bvadd ((_ zero_extend 1) r11_2) ((_ zero_extend 1) rax_2)))) (= rax_3 ((_ extract 63 0) (bvadd ((_ zero_extend 1) r11_2) ((_ zero_extend 1) rax_2))))))
(assert (and (= carry2_1 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) #x0000000000000000) ((_ zero_extend 1) rdx_2)) ((_ zero_extend 64) carry_3)))) (= rdx_3 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) #x0000000000000000) ((_ zero_extend 1) rdx_2)) ((_ zero_extend 64) carry_3))))))
(assert true)
(assert true)
(assert (= rax_5 (bvand #x7FFFFFFFFFFFFFFF rdx_3)))
(assert (= carry_4 ((_ zero_extend 63) carry_3)))
(assert true)
(assert true)
(assert (and (= carry_5 ((_ extract 64 64) (bvadd ((_ zero_extend 1) L0x7fffffffe360_0) ((_ zero_extend 1) L0x7fffffffe340_0)))) (= rsi_2 ((_ extract 63 0) (bvadd ((_ zero_extend 1) L0x7fffffffe360_0) ((_ zero_extend 1) L0x7fffffffe340_0))))))
(assert (and (= carry_6 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) L0x7fffffffe368_0) ((_ zero_extend 1) L0x7fffffffe348_0)) ((_ zero_extend 64) carry_5)))) (= rdi_2 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) L0x7fffffffe368_0) ((_ zero_extend 1) L0x7fffffffe348_0)) ((_ zero_extend 64) carry_5))))))
(assert true)
(assert true)
(assert (and (= rax_8 ((_ zero_extend 63) ((_ extract 63 63) rdi_2))) (= tmp_2 ((_ zero_extend 1) ((_ extract 62 0) rdi_2)))))
(assert (and (= carry_7 ((_ extract 64 64) (bvadd ((_ zero_extend 1) rsi_2) ((_ zero_extend 1) rax_8)))) (= rax_9 ((_ extract 63 0) (bvadd ((_ zero_extend 1) rsi_2) ((_ zero_extend 1) rax_8))))))
(assert (and (= carry2_2 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) rdi_2) ((_ zero_extend 1) #x0000000000000000)) ((_ zero_extend 64) carry_7)))) (= rdx_6 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) rdi_2) ((_ zero_extend 1) #x0000000000000000)) ((_ zero_extend 64) carry_7))))))
(assert true)
(assert true)
(assert (= r8_2 (bvand rdx_6 #x7FFFFFFFFFFFFFFF)))
(assert (= carry_8 ((_ zero_extend 63) carry_7)))
(assert true)
(assert true)
(assert (not (bvult (bvadd (bvmul ((_ zero_extend 64) rax_9) #x00000000000000000000000000000001) (bvmul ((_ zero_extend 64) r8_2) #x00000000000000010000000000000000)) #x80000000000000000000000000000000)))
(check-sat)
(exit)
