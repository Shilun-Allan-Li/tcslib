/-- A known row-vector action commutes with the source-group implicit representation
[Wee20, §2.1, p. 4].

**Proof sketch.** At each column apply `groupDot_expVec`, commuting scalar factors. -/
theorem expVec_vecMul [Fintype ι] (g : B.G) (a : ι → ZMod B.order)
    (M : Matrix ι κ (ZMod B.order)) :
    groupVecMul a (B.expMat g M) = B.expVec g (a ᵥ* M) :=
  funext fun j =>
    (groupVecMul_apply a (B.expMat g M) j).trans
      ((congrArg (fun column : ι → B.G => groupDot column a)
        (funext fun i => (B.expMat_apply g M i j).trans
          (B.expVec_apply g (fun i => M i j) i).symm)).trans
        ((B.groupDot_expVec g (fun i => M i j) a).trans
          ((congrArg (fun x : ZMod B.order => g ^ x.val)
            (dotProduct_comm (fun i => M i j) a)).trans
            (show g ^ (dotProduct a (fun i => M i j)).val = B.expVec g (a ᵥ* M) j from
              (B.expVec_apply g (a ᵥ* M) j).symm))))
