/-- A scalar matrix on the left can be applied to a group-valued implicit matrix
[Wee20, §4.2, p. 10, (12)].

**Proof sketch.** Apply the vector dot-product law entrywise and commute scalar factors. -/
theorem expMat_mul_left [Fintype κ] (g : B.G) (M : Matrix ι κ (ZMod B.order))
    (N : Matrix κ υ (ZMod B.order)) :
    matMulGroup M (B.expMat g N) = B.expMat g (M * N) :=
  funext fun i => funext fun j =>
    (matMulGroup_apply M (B.expMat g N) i j).trans
      ((congrArg (fun column : κ → B.G => groupDot column (M i))
        (funext fun k => (B.expMat_apply g N k j).trans
          (B.expVec_apply g (fun k => N k j) k).symm)).trans
        ((B.groupDot_expVec g (fun k => N k j) (M i)).trans
          ((congrArg (fun x : ZMod B.order => g ^ x.val)
            (dotProduct_comm (fun k => N k j) (M i))).trans
            ((congrArg (fun x : ZMod B.order => g ^ x.val)
              (Matrix.mul_apply' (M := M) (N := N) (i := i) (k := j)).symm).trans
              (B.expMat_apply g (M * N) i j).symm))))
