/-- Known powers also implement a target-group matrix-vector action
[Wee20, §4.2, p. 9, (8)].

**Proof sketch.** Apply `groupDot_expVecT` to every row. -/
theorem expMatT_mulVec [Fintype κ] (gT : B.GT) (M : Matrix ι κ (ZMod B.order))
    (a : κ → ZMod B.order) :
    groupMulVec (B.expMatT gT M) a = B.expVecT gT (M *ᵥ a) :=
  funext fun i =>
    (groupMulVec_apply (B.expMatT gT M) a i).trans
      ((congrArg (fun row : κ → B.GT => groupDot row a)
        (funext fun k => (B.expMatT_apply gT M i k).trans
          (B.expVecT_apply gT (M i) k).symm)).trans
        ((B.groupDot_expVecT gT (M i) a).trans
          (show gT ^ (dotProduct (M i) a).val = B.expVecT gT (M *ᵥ a) i from
            (B.expVecT_apply gT (M *ᵥ a) i).symm)))
