
/-! Liveness pair (gsw-6b-u12, C6), appended to the owner's own probe: a foreign definition read
by `rfl` (negative: closes unsealed, fails exactly once sealed) and the same fact through its
published reader (positive: closes sealed). -/

-- NEG BranchingProgram.evalWith by rfl
example {w n : ℕ} (B : BranchingProgram w n) (x : Fin n → Bool) (V : Fin w → ℕ) :
    B.evalWith (fun b (u v : ℕ) => if b then v else u) x V =
      B.instrs.foldl (fun U ι => ι.stepWith (fun b (u v : ℕ) => if b then v else u) x U) V :=
  rfl
-- POS BranchingProgram.evalWith through evalWith_eq
example {w n : ℕ} (B : BranchingProgram w n) (x : Fin n → Bool) (V : Fin w → ℕ) :
    B.evalWith (fun b (u v : ℕ) => if b then v else u) x V =
      B.instrs.foldl (fun U ι => ι.stepWith (fun b (u v : ℕ) => if b then v else u) x U) V :=
  BranchingProgram.evalWith_eq _ x B V
