/-- A known column-vector action commutes with the source-group implicit representation
[Wee20, §2.1, p. 4].

**Proof sketch.** At each row apply `groupDot_expVec` to the defining scalar dot product. -/
theorem expMat_mulVec [Fintype κ] (g : B.G) (M : Matrix ι κ (ZMod B.order))
    (a : κ → ZMod B.order) :
    groupMulVec (B.expMat g M) a = B.expVec g (M *ᵥ a) :=
  funext fun i =>
    (groupMulVec_apply (B.expMat g M) a i).trans
      ((congrArg (fun row : κ → B.G => groupDot row a)
        (funext fun k => (B.expMat_apply g M i k).trans
          (B.expVec_apply g (M i) k).symm)).trans
        ((B.groupDot_expVec g (M i) a).trans
          (show g ^ (dotProduct (M i) a).val = B.expVec g (M *ᵥ a) i from
            (B.expVec_apply g (M *ᵥ a) i).symm)))
