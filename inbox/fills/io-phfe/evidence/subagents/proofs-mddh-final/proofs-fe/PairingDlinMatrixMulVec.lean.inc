/-- The real DLIN vector is the DLIN matrix applied to its two random scalars
[GJLS21, Definition 3.3, p. 18; JLS26, §1.1, p. 3].

**Proof sketch.** Read the three rows and the two column-vector coordinates; the three dot
products reduce to `a*r`, `b*s`, and `r+s`. -/
theorem dlinMatrix_mulVec {p : ℕ} (a b r s : ZMod p) :
    dlinMatrix a b *ᵥ ![r, s] = ![a * r, b * s, r + s] := by
  rw [dlinMatrix_eq]
  change (Matrix.of ![![a, 0], ![0, b], ![1, 1]]) *ᵥ ![r, s] = _
  simp only [Matrix.cons_mulVec, Matrix.empty_mulVec, Matrix.vec2_dotProduct',
    zero_mul, one_mul, add_zero, zero_add]
