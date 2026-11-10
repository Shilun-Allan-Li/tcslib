import TCSlib.Cryptography.Games.OracleComp

set_option maxHeartbeats 0

open TCSlib.Cryptography.Games

attribute [local irreducible] OracleComp.CostBoundedBy

/-- Multiplying every oracle cost by a common factor multiplies the bound by that factor. -/
theorem scaledCostProbe {ι α : Type} {spec : OracleSpec ι} {cost : ι → ℕ}
    {c : OracleComp spec α} {q : ℕ} (h : OracleComp.CostBoundedBy cost c q) (scale : ℕ) :
    OracleComp.CostBoundedBy (fun i => scale * cost i) c (scale * q) := by
  first
  | exact?
  | induction c generalizing q with
    | pure a => exact OracleComp.costBoundedBy_pure _ _ _
    | query i x k ih =>
      obtain ⟨hi, hk⟩ := (OracleComp.costBoundedBy_query cost i x k q).1 h
      apply (OracleComp.costBoundedBy_query (fun j => scale * cost j) i x k (scale * q)).2
      refine ⟨Nat.mul_le_mul_left scale hi, fun y => ?_⟩
      rw [← Nat.mul_sub_left_distrib]
      exact ih y (hk y)

#print axioms scaledCostProbe
