/-- Successive known scalar row/matrix weights on an arbitrary source-group matrix
compose by ordinary scalar matrix multiplication. This is technical implicit arithmetic
for [Wee20, §2.1, p.4; §4.2, p.9]. The group matrix remains arbitrary.

**Proof sketch.** Read groupVecMul_apply, matMulGroup_apply and groupDot_eq. Distribute
known powers over products, interchange the two finite products, use pow_val_mul to
combine known scalar weights, and use the modular additive exponent law to collect
each column's scalar sum. Reuse finite-product and scalar vecMul equations. -/
theorem groupVecMul_matMulGroup [Fintype ι] [Fintype κ]
    (v : ι → ZMod B.order) (W : Matrix ι κ (ZMod B.order))
    (M : Matrix κ υ B.G) :
    groupVecMul v (matMulGroup W M) = groupVecMul (Matrix.vecMul v W) M := by
  funext j
  simp only [groupVecMul_apply, matMulGroup_apply, groupDot_eq, ← Finset.prod_pow]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro k _
  show (∏ i, (M k j ^ (W i k).val) ^ (v i).val) =
    M k j ^ (dotProduct v (fun i => W i k)).val
  have h := B.groupDot_expVec (M k j) (fun i => W i k) v
  simp only [groupDot_eq, B.expVec_apply] at h
  exact h.trans (congrArg (fun c : ZMod B.order => M k j ^ c.val)
    (dotProduct_comm (fun i => W i k) v))
