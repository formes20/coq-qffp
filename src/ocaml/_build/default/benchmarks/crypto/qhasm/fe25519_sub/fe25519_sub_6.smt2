(set-logic QF_BV)
(set-info :smt-lib-version 2.0)
(declare-fun y4_0 () (_ BitVec 64))
(declare-fun y3_0 () (_ BitVec 64))
(declare-fun y2_0 () (_ BitVec 64))
(declare-fun y1_0 () (_ BitVec 64))
(declare-fun y0_0 () (_ BitVec 64))
(declare-fun x4_0 () (_ BitVec 64))
(declare-fun x3_0 () (_ BitVec 64))
(declare-fun x2_0 () (_ BitVec 64))
(declare-fun x1_0 () (_ BitVec 64))
(declare-fun x0_0 () (_ BitVec 64))
(declare-fun r4_3 () (_ BitVec 64))
(declare-fun r4_2 () (_ BitVec 64))
(declare-fun r3_3 () (_ BitVec 64))
(declare-fun r3_2 () (_ BitVec 64))
(declare-fun r2_3 () (_ BitVec 64))
(declare-fun r2_2 () (_ BitVec 64))
(declare-fun r1_3 () (_ BitVec 64))
(declare-fun r1_2 () (_ BitVec 64))
(declare-fun r0_3 () (_ BitVec 64))
(declare-fun r0_2 () (_ BitVec 64))
(assert (and (and (and (and (and (and (and (and (and (bvule x0_0 #x0008000000008000) (bvule x1_0 #x0008000000008000)) (bvule x2_0 #x0008000000008000)) (bvule x3_0 #x0008000000008000)) (bvule x4_0 #x0008000000008000)) (bvule y0_0 #x0008000000008000)) (bvule y1_0 #x0008000000008000)) (bvule y2_0 #x0008000000008000)) (bvule y3_0 #x0008000000008000)) (bvule y4_0 #x0008000000008000)))
(assert (= r0_2 (bvadd x0_0 #x000FFFFFFFFFFFDA)))
(assert (= r1_2 (bvadd x1_0 #x000FFFFFFFFFFFFE)))
(assert (= r2_2 (bvadd x2_0 #x000FFFFFFFFFFFFE)))
(assert (= r3_2 (bvadd x3_0 #x000FFFFFFFFFFFFE)))
(assert (= r4_2 (bvadd x4_0 #x000FFFFFFFFFFFFE)))
(assert (= r0_3 (bvsub r0_2 y0_0)))
(assert (= r1_3 (bvsub r1_2 y1_0)))
(assert (= r2_3 (bvsub r2_2 y2_0)))
(assert (= r3_3 (bvsub r3_2 y3_0)))
(assert (= r4_3 (bvsub r4_2 y4_0)))
(assert (not (bvult r4_3 #x0040000000000000)))
(check-sat)
(exit)
