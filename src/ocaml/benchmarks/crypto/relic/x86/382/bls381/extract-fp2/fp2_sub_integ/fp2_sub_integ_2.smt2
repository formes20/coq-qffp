(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(declare-fun rcx_4 () (_ BitVec 64))
(declare-fun rcx_2 () (_ BitVec 64))
(declare-fun rax_4 () (_ BitVec 64))
(declare-fun rax_2 () (_ BitVec 64))
(declare-fun r9_4 () (_ BitVec 64))
(declare-fun r9_2 () (_ BitVec 64))
(declare-fun r8_28 () (_ BitVec 64))
(declare-fun r8_26 () (_ BitVec 64))
(declare-fun r8_24 () (_ BitVec 64))
(declare-fun r8_22 () (_ BitVec 64))
(declare-fun r8_20 () (_ BitVec 64))
(declare-fun r8_18 () (_ BitVec 64))
(declare-fun r8_16 () (_ BitVec 64))
(declare-fun r8_14 () (_ BitVec 64))
(declare-fun r8_12 () (_ BitVec 64))
(declare-fun r8_10 () (_ BitVec 64))
(declare-fun r8_8 () (_ BitVec 64))
(declare-fun r8_6 () (_ BitVec 64))
(declare-fun r8_4 () (_ BitVec 64))
(declare-fun r8_2 () (_ BitVec 64))
(declare-fun r11_4 () (_ BitVec 64))
(declare-fun r11_2 () (_ BitVec 64))
(declare-fun r10_4 () (_ BitVec 64))
(declare-fun r10_2 () (_ BitVec 64))
(declare-fun carry_24 () (_ BitVec 1))
(declare-fun carry_23 () (_ BitVec 1))
(declare-fun carry_22 () (_ BitVec 1))
(declare-fun carry_21 () (_ BitVec 1))
(declare-fun carry_20 () (_ BitVec 1))
(declare-fun carry_19 () (_ BitVec 1))
(declare-fun carry_18 () (_ BitVec 1))
(declare-fun carry_17 () (_ BitVec 1))
(declare-fun carry_16 () (_ BitVec 1))
(declare-fun carry_15 () (_ BitVec 1))
(declare-fun carry_14 () (_ BitVec 1))
(declare-fun carry_13 () (_ BitVec 1))
(declare-fun carry_12 () (_ BitVec 1))
(declare-fun carry_11 () (_ BitVec 1))
(declare-fun carry_10 () (_ BitVec 1))
(declare-fun carry_9 () (_ BitVec 1))
(declare-fun carry_8 () (_ BitVec 1))
(declare-fun carry_7 () (_ BitVec 1))
(declare-fun carry_6 () (_ BitVec 1))
(declare-fun carry_5 () (_ BitVec 1))
(declare-fun carry_4 () (_ BitVec 1))
(declare-fun carry_3 () (_ BitVec 1))
(declare-fun carry_2 () (_ BitVec 1))
(declare-fun carry_1 () (_ BitVec 1))
(declare-fun b2_5_0 () (_ BitVec 64))
(declare-fun b2_4_0 () (_ BitVec 64))
(declare-fun b2_3_0 () (_ BitVec 64))
(declare-fun b2_2_0 () (_ BitVec 64))
(declare-fun b2_1_0 () (_ BitVec 64))
(declare-fun b2_0_0 () (_ BitVec 64))
(declare-fun b1_5_0 () (_ BitVec 64))
(declare-fun b1_4_0 () (_ BitVec 64))
(declare-fun b1_3_0 () (_ BitVec 64))
(declare-fun b1_2_0 () (_ BitVec 64))
(declare-fun b1_1_0 () (_ BitVec 64))
(declare-fun b1_0_0 () (_ BitVec 64))
(declare-fun a2_5_0 () (_ BitVec 64))
(declare-fun a2_4_0 () (_ BitVec 64))
(declare-fun a2_3_0 () (_ BitVec 64))
(declare-fun a2_2_0 () (_ BitVec 64))
(declare-fun a2_1_0 () (_ BitVec 64))
(declare-fun a2_0_0 () (_ BitVec 64))
(declare-fun a1_5_0 () (_ BitVec 64))
(declare-fun a1_4_0 () (_ BitVec 64))
(declare-fun a1_3_0 () (_ BitVec 64))
(declare-fun a1_2_0 () (_ BitVec 64))
(declare-fun a1_1_0 () (_ BitVec 64))
(declare-fun a1_0_0 () (_ BitVec 64))
(declare-fun L0x7fffffffdda8_2 () (_ BitVec 64))
(declare-fun L0x7fffffffdda0_2 () (_ BitVec 64))
(declare-fun L0x7fffffffdd98_2 () (_ BitVec 64))
(declare-fun L0x7fffffffdd90_2 () (_ BitVec 64))
(declare-fun L0x7fffffffdd88_2 () (_ BitVec 64))
(declare-fun L0x7fffffffdd80_2 () (_ BitVec 64))
(declare-fun L0x7fffffffdd78_2 () (_ BitVec 64))
(declare-fun L0x7fffffffdd70_2 () (_ BitVec 64))
(declare-fun L0x7fffffffdd68_2 () (_ BitVec 64))
(declare-fun L0x7fffffffdd60_2 () (_ BitVec 64))
(declare-fun L0x7fffffffdd58_2 () (_ BitVec 64))
(declare-fun L0x7fffffffdd50_2 () (_ BitVec 64))
(assert (and (and (and (bvult (bvadd (bvmul ((_ zero_extend 320) a1_0_0) #x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 320) a1_1_0) #x000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 320) a1_2_0) #x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) a1_3_0) #x000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) a1_4_0) #x000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000) (bvmul ((_ zero_extend 320) a1_5_0) #x000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000)))))) (bvadd (bvmul ((_ zero_extend 320) #xB9FEFFFFFFFFAAAB) #x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 320) #x1EABFFFEB153FFFF) #x000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 320) #x6730D2A0F6B0F624) #x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) #x64774B84F38512BF) #x000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) #x4B1BA7B6434BACD7) #x000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000) (bvmul ((_ zero_extend 320) #x1A0111EA397FE69A) #x000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000))))))) (bvult (bvadd (bvmul ((_ zero_extend 320) b1_0_0) #x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 320) b1_1_0) #x000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 320) b1_2_0) #x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) b1_3_0) #x000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) b1_4_0) #x000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000) (bvmul ((_ zero_extend 320) b1_5_0) #x000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000)))))) (bvadd (bvmul ((_ zero_extend 320) #xB9FEFFFFFFFFAAAB) #x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 320) #x1EABFFFEB153FFFF) #x000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 320) #x6730D2A0F6B0F624) #x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) #x64774B84F38512BF) #x000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) #x4B1BA7B6434BACD7) #x000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000) (bvmul ((_ zero_extend 320) #x1A0111EA397FE69A) #x000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000)))))))) (bvult (bvadd (bvmul ((_ zero_extend 320) a2_0_0) #x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 320) a2_1_0) #x000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 320) a2_2_0) #x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) a2_3_0) #x000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) a2_4_0) #x000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000) (bvmul ((_ zero_extend 320) a2_5_0) #x000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000)))))) (bvadd (bvmul ((_ zero_extend 320) #xB9FEFFFFFFFFAAAB) #x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 320) #x1EABFFFEB153FFFF) #x000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 320) #x6730D2A0F6B0F624) #x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) #x64774B84F38512BF) #x000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) #x4B1BA7B6434BACD7) #x000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000) (bvmul ((_ zero_extend 320) #x1A0111EA397FE69A) #x000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000)))))))) (bvult (bvadd (bvmul ((_ zero_extend 320) b2_0_0) #x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 320) b2_1_0) #x000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 320) b2_2_0) #x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) b2_3_0) #x000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) b2_4_0) #x000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000) (bvmul ((_ zero_extend 320) b2_5_0) #x000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000)))))) (bvadd (bvmul ((_ zero_extend 320) #xB9FEFFFFFFFFAAAB) #x000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 320) #x1EABFFFEB153FFFF) #x000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 320) #x6730D2A0F6B0F624) #x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) #x64774B84F38512BF) #x000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 320) #x4B1BA7B6434BACD7) #x000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000) (bvmul ((_ zero_extend 320) #x1A0111EA397FE69A) #x000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000)))))))))
(assert (and (= carry_1 ((_ extract 64 64) (bvsub ((_ zero_extend 1) a2_0_0) ((_ zero_extend 1) b2_0_0)))) (= r8_2 ((_ extract 63 0) (bvsub ((_ zero_extend 1) a2_0_0) ((_ zero_extend 1) b2_0_0))))))
(assert (and (= carry_2 ((_ extract 64 64) (bvsub ((_ zero_extend 1) a2_1_0) (bvadd ((_ zero_extend 1) b2_1_0) ((_ zero_extend 64) carry_1))))) (= r8_4 ((_ extract 63 0) (bvsub ((_ zero_extend 1) a2_1_0) (bvadd ((_ zero_extend 1) b2_1_0) ((_ zero_extend 64) carry_1)))))))
(assert (and (= carry_3 ((_ extract 64 64) (bvsub ((_ zero_extend 1) a2_2_0) (bvadd ((_ zero_extend 1) b2_2_0) ((_ zero_extend 64) carry_2))))) (= r8_6 ((_ extract 63 0) (bvsub ((_ zero_extend 1) a2_2_0) (bvadd ((_ zero_extend 1) b2_2_0) ((_ zero_extend 64) carry_2)))))))
(assert (and (= carry_4 ((_ extract 64 64) (bvsub ((_ zero_extend 1) a2_3_0) (bvadd ((_ zero_extend 1) b2_3_0) ((_ zero_extend 64) carry_3))))) (= r8_8 ((_ extract 63 0) (bvsub ((_ zero_extend 1) a2_3_0) (bvadd ((_ zero_extend 1) b2_3_0) ((_ zero_extend 64) carry_3)))))))
(assert (and (= carry_5 ((_ extract 64 64) (bvsub ((_ zero_extend 1) a2_4_0) (bvadd ((_ zero_extend 1) b2_4_0) ((_ zero_extend 64) carry_4))))) (= r8_10 ((_ extract 63 0) (bvsub ((_ zero_extend 1) a2_4_0) (bvadd ((_ zero_extend 1) b2_4_0) ((_ zero_extend 64) carry_4)))))))
(assert (and (= carry_6 ((_ extract 64 64) (bvsub ((_ zero_extend 1) a2_5_0) (bvadd ((_ zero_extend 1) b2_5_0) ((_ zero_extend 64) carry_5))))) (= r8_12 ((_ extract 63 0) (bvsub ((_ zero_extend 1) a2_5_0) (bvadd ((_ zero_extend 1) b2_5_0) ((_ zero_extend 64) carry_5)))))))
(assert (= rax_2 (ite (= carry_6 #b1) #xB9FEFFFFFFFFAAAB #x0000000000000000)))
(assert (= rcx_2 (ite (= carry_6 #b1) #x1EABFFFEB153FFFF #x0000000000000000)))
(assert (= r8_14 (ite (= carry_6 #b1) #x6730D2A0F6B0F624 #x0000000000000000)))
(assert (= r9_2 (ite (= carry_6 #b1) #x64774B84F38512BF #x0000000000000000)))
(assert (= r10_2 (ite (= carry_6 #b1) #x4B1BA7B6434BACD7 #x0000000000000000)))
(assert (= r11_2 (ite (= carry_6 #b1) #x1A0111EA397FE69A #x0000000000000000)))
(assert (and (= carry_7 ((_ extract 64 64) (bvadd ((_ zero_extend 1) r8_2) ((_ zero_extend 1) rax_2)))) (= L0x7fffffffdd50_2 ((_ extract 63 0) (bvadd ((_ zero_extend 1) r8_2) ((_ zero_extend 1) rax_2))))))
(assert (and (= carry_8 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) r8_4) ((_ zero_extend 1) rcx_2)) ((_ zero_extend 64) carry_7)))) (= L0x7fffffffdd58_2 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) r8_4) ((_ zero_extend 1) rcx_2)) ((_ zero_extend 64) carry_7))))))
(assert (and (= carry_9 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) r8_6) ((_ zero_extend 1) r8_14)) ((_ zero_extend 64) carry_8)))) (= L0x7fffffffdd60_2 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) r8_6) ((_ zero_extend 1) r8_14)) ((_ zero_extend 64) carry_8))))))
(assert (and (= carry_10 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) r8_8) ((_ zero_extend 1) r9_2)) ((_ zero_extend 64) carry_9)))) (= L0x7fffffffdd68_2 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) r8_8) ((_ zero_extend 1) r9_2)) ((_ zero_extend 64) carry_9))))))
(assert (and (= carry_11 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) r8_10) ((_ zero_extend 1) r10_2)) ((_ zero_extend 64) carry_10)))) (= L0x7fffffffdd70_2 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) r8_10) ((_ zero_extend 1) r10_2)) ((_ zero_extend 64) carry_10))))))
(assert (and (= carry_12 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) r8_12) ((_ zero_extend 1) r11_2)) ((_ zero_extend 64) carry_11)))) (= L0x7fffffffdd78_2 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) r8_12) ((_ zero_extend 1) r11_2)) ((_ zero_extend 64) carry_11))))))
(assert true)
(assert true)
(assert (and (= carry_13 ((_ extract 64 64) (bvsub ((_ zero_extend 1) a1_0_0) ((_ zero_extend 1) b1_0_0)))) (= r8_16 ((_ extract 63 0) (bvsub ((_ zero_extend 1) a1_0_0) ((_ zero_extend 1) b1_0_0))))))
(assert (and (= carry_14 ((_ extract 64 64) (bvsub ((_ zero_extend 1) a1_1_0) (bvadd ((_ zero_extend 1) b1_1_0) ((_ zero_extend 64) carry_13))))) (= r8_18 ((_ extract 63 0) (bvsub ((_ zero_extend 1) a1_1_0) (bvadd ((_ zero_extend 1) b1_1_0) ((_ zero_extend 64) carry_13)))))))
(assert (and (= carry_15 ((_ extract 64 64) (bvsub ((_ zero_extend 1) a1_2_0) (bvadd ((_ zero_extend 1) b1_2_0) ((_ zero_extend 64) carry_14))))) (= r8_20 ((_ extract 63 0) (bvsub ((_ zero_extend 1) a1_2_0) (bvadd ((_ zero_extend 1) b1_2_0) ((_ zero_extend 64) carry_14)))))))
(assert (and (= carry_16 ((_ extract 64 64) (bvsub ((_ zero_extend 1) a1_3_0) (bvadd ((_ zero_extend 1) b1_3_0) ((_ zero_extend 64) carry_15))))) (= r8_22 ((_ extract 63 0) (bvsub ((_ zero_extend 1) a1_3_0) (bvadd ((_ zero_extend 1) b1_3_0) ((_ zero_extend 64) carry_15)))))))
(assert (and (= carry_17 ((_ extract 64 64) (bvsub ((_ zero_extend 1) a1_4_0) (bvadd ((_ zero_extend 1) b1_4_0) ((_ zero_extend 64) carry_16))))) (= r8_24 ((_ extract 63 0) (bvsub ((_ zero_extend 1) a1_4_0) (bvadd ((_ zero_extend 1) b1_4_0) ((_ zero_extend 64) carry_16)))))))
(assert (and (= carry_18 ((_ extract 64 64) (bvsub ((_ zero_extend 1) a1_5_0) (bvadd ((_ zero_extend 1) b1_5_0) ((_ zero_extend 64) carry_17))))) (= r8_26 ((_ extract 63 0) (bvsub ((_ zero_extend 1) a1_5_0) (bvadd ((_ zero_extend 1) b1_5_0) ((_ zero_extend 64) carry_17)))))))
(assert (= rax_4 (ite (= carry_18 #b1) #xB9FEFFFFFFFFAAAB #x0000000000000000)))
(assert (= rcx_4 (ite (= carry_18 #b1) #x1EABFFFEB153FFFF #x0000000000000000)))
(assert (= r8_28 (ite (= carry_18 #b1) #x6730D2A0F6B0F624 #x0000000000000000)))
(assert (= r9_4 (ite (= carry_18 #b1) #x64774B84F38512BF #x0000000000000000)))
(assert (= r10_4 (ite (= carry_18 #b1) #x4B1BA7B6434BACD7 #x0000000000000000)))
(assert (= r11_4 (ite (= carry_18 #b1) #x1A0111EA397FE69A #x0000000000000000)))
(assert (and (= carry_19 ((_ extract 64 64) (bvadd ((_ zero_extend 1) r8_16) ((_ zero_extend 1) rax_4)))) (= L0x7fffffffdd80_2 ((_ extract 63 0) (bvadd ((_ zero_extend 1) r8_16) ((_ zero_extend 1) rax_4))))))
(assert (and (= carry_20 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) r8_18) ((_ zero_extend 1) rcx_4)) ((_ zero_extend 64) carry_19)))) (= L0x7fffffffdd88_2 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) r8_18) ((_ zero_extend 1) rcx_4)) ((_ zero_extend 64) carry_19))))))
(assert (and (= carry_21 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) r8_20) ((_ zero_extend 1) r8_28)) ((_ zero_extend 64) carry_20)))) (= L0x7fffffffdd90_2 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) r8_20) ((_ zero_extend 1) r8_28)) ((_ zero_extend 64) carry_20))))))
(assert (and (= carry_22 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) r8_22) ((_ zero_extend 1) r9_4)) ((_ zero_extend 64) carry_21)))) (= L0x7fffffffdd98_2 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) r8_22) ((_ zero_extend 1) r9_4)) ((_ zero_extend 64) carry_21))))))
(assert (and (= carry_23 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) r8_24) ((_ zero_extend 1) r10_4)) ((_ zero_extend 64) carry_22)))) (= L0x7fffffffdda0_2 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) r8_24) ((_ zero_extend 1) r10_4)) ((_ zero_extend 64) carry_22))))))
(assert (and (= carry_24 ((_ extract 64 64) (bvadd (bvadd ((_ zero_extend 1) r8_26) ((_ zero_extend 1) r11_4)) ((_ zero_extend 64) carry_23)))) (= L0x7fffffffdda8_2 ((_ extract 63 0) (bvadd (bvadd ((_ zero_extend 1) r8_26) ((_ zero_extend 1) r11_4)) ((_ zero_extend 64) carry_23))))))
(assert true)
(assert true)
(assert (not (= (bvsmod (bvsub (bvadd (bvmul ((_ zero_extend 384) L0x7fffffffdd80_2) #x0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 384) L0x7fffffffdd88_2) #x0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 384) L0x7fffffffdd90_2) #x0000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 384) L0x7fffffffdd98_2) #x0000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 384) L0x7fffffffdda0_2) #x0000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 384) L0x7fffffffdda8_2) #x0000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000) (bvmul ((_ zero_extend 384) #x0000000000000000) #x0000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))))))) (bvsub (bvadd (bvmul ((_ zero_extend 384) a1_0_0) #x0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 384) a1_1_0) #x0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 384) a1_2_0) #x0000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 384) a1_3_0) #x0000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 384) a1_4_0) #x0000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 384) a1_5_0) #x0000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000) (bvmul ((_ zero_extend 384) #x0000000000000000) #x0000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))))))) (bvadd (bvmul ((_ zero_extend 384) b1_0_0) #x0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 384) b1_1_0) #x0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 384) b1_2_0) #x0000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 384) b1_3_0) #x0000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 384) b1_4_0) #x0000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 384) b1_5_0) #x0000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000) (bvmul ((_ zero_extend 384) #x0000000000000000) #x0000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))))))))) (bvadd (bvmul ((_ zero_extend 384) #xB9FEFFFFFFFFAAAB) #x0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001) (bvadd (bvmul ((_ zero_extend 384) #x1EABFFFEB153FFFF) #x0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000) (bvadd (bvmul ((_ zero_extend 384) #x6730D2A0F6B0F624) #x0000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 384) #x64774B84F38512BF) #x0000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 384) #x4B1BA7B6434BACD7) #x0000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000) (bvadd (bvmul ((_ zero_extend 384) #x1A0111EA397FE69A) #x0000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000000000000000) (bvmul ((_ zero_extend 384) #x0000000000000000) #x0000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))))))) #x0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))
(check-sat)
(exit)