/-- Pairing implicit rows and columns evaluates the scalar matrix product
[Wee20, §2.1, p. 4; §4.2, p. 9, (6)–(7)].

**Proof sketch.** Apply `pair_expVec` to each row-column entry. -/
theorem pair_expMat [Fintype κ] (g h : B.G) (M : Matrix ι κ (ZMod B.order))
    (N : Matrix κ υ (ZMod B.order)) :
    B.pairMat (B.expMat g M) (B.expMat h N) = B.expMatT (B.pair g h) (M * N) :=
  funext fun i => funext fun j =>
    (B.pairMat_apply (B.expMat g M) (B.expMat h N) i j).trans
      ((congrArg₂ B.pairVec
        (funext fun k => (B.expMat_apply g M i k).trans
          (B.expVec_apply g (M i) k).symm)
        (funext fun k => (B.expMat_apply h N k j).trans
          (B.expVec_apply h (fun k => N k j) k).symm)).trans
        ((B.pair_expVec g h (M i) (fun k => N k j)).trans
          ((congrArg (fun x : ZMod B.order => B.pair g h ^ x.val)
            (Matrix.mul_apply' (M := M) (N := N) (i := i) (k := j)).symm).trans
            (B.expMatT_apply (B.pair g h) (M * N) i j).symm)))
