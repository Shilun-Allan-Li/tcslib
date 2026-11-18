/-- A scalar matrix on the right can be applied to a group-valued implicit matrix
[Wee20, §4.2, p. 9, KeyGen].

**Proof sketch.** Apply the vector dot-product law to every row-column entry. -/
theorem expMat_mul [Fintype κ] (g : B.G) (M : Matrix ι κ (ZMod B.order))
    (N : Matrix κ υ (ZMod B.order)) :
    groupMatMul (B.expMat g M) N = B.expMat g (M * N) :=
  funext fun i => funext fun j =>
    (groupMatMul_apply (B.expMat g M) N i j).trans
      ((congrArg (fun row : κ → B.G => groupDot row (fun k => N k j))
        (funext fun k => (B.expMat_apply g M i k).trans
          (B.expVec_apply g (M i) k).symm)).trans
        ((B.groupDot_expVec g (M i) (fun k => N k j)).trans
          ((congrArg (fun x : ZMod B.order => g ^ x.val)
            (Matrix.mul_apply' (M := M) (N := N) (i := i) (k := j)).symm).trans
            (B.expMat_apply g (M * N) i j).symm)))
