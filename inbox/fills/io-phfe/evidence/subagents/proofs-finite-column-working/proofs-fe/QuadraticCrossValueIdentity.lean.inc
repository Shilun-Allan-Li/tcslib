/-- Evaluating the cross-term identity isolates the desired private quadratic value
[Wee20, §3.1, p. 6, (5)].

**Proof sketch.** Take the scalar dot product of `cross_tensor_identity` with the supplied
function vector. Reuse dot-product linearity and matrix-action associativity, then rearrange. -/
theorem cross_value_identity {p : ℕ+} {n1 n2 : ℕ}
    (A1 : Matrix (Fin 2) (Fin n1) (ZMod (p : ℕ)))
    (A2 : Matrix (Fin 2) (Fin n2) (ZMod (p : ℕ)))
    (s1 s2 : Fin 2 → ZMod (p : ℕ)) (z1 : Fin n1 → ZMod (p : ℕ))
    (z2 : Fin n2 → ZMod (p : ℕ)) (fx : Fin (n1 * n2) → ZMod (p : ℕ)) :
    let y1 := Matrix.vecMul s1 A1 + z1
    let y2 := Matrix.vecMul s2 A2 + z2
    dotProduct (privateTensor (p := p) z1 z2) fx =
      dotProduct (privateTensor (p := p) y1 y2) fx -
        dotProduct (signalScalar (p := p) s1 z2 y1 s2)
          (mixScalar (p := p) A1 A2 *ᵥ fx) := by
  have h := congrArg (fun v : Fin (n1 * n2) → ZMod (p : ℕ) => dotProduct v fx)
    (cross_tensor_identity A1 A2 s1 s2 z1 z2)
  change dotProduct
      (privateTensor (p := p) (Matrix.vecMul s1 A1 + z1) (Matrix.vecMul s2 A2 + z2)) fx =
    dotProduct (privateTensor (p := p) z1 z2 +
      Matrix.vecMul (signalScalar (p := p) s1 z2 (Matrix.vecMul s1 A1 + z1) s2)
        (mixScalar (p := p) A1 A2)) fx at h
  rw [add_dotProduct, ← Matrix.dotProduct_mulVec] at h
  exact eq_sub_of_add_eq h.symm
