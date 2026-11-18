/-- The two cross terms account for the masked tensor product
[Wee20, §3.1, p. 6, (4)].

**Proof sketch.** Reindex by the canonical output pair. Apply the mixed-product property
to each Kronecker block. The two block contributions are `(s1 A1)⊗z2` and `y1⊗(s2 A2)`.
Expand `y1=s1 A1+z1` and `y2=s2 A2+z2`; distributivity gives the identity. -/
theorem cross_tensor_identity {p : ℕ+} {n1 n2 : ℕ}
    (A1 : Matrix (Fin 2) (Fin n1) (ZMod (p : ℕ)))
    (A2 : Matrix (Fin 2) (Fin n2) (ZMod (p : ℕ)))
    (s1 s2 : Fin 2 → ZMod (p : ℕ)) (z1 : Fin n1 → ZMod (p : ℕ))
    (z2 : Fin n2 → ZMod (p : ℕ)) :
    let y1 := Matrix.vecMul s1 A1 + z1
    let y2 := Matrix.vecMul s2 A2 + z2
    privateTensor (p := p) y1 y2 = privateTensor (p := p) z1 z2 +
      Matrix.vecMul (signalScalar (p := p) s1 z2 y1 s2) (mixScalar (p := p) A1 A2) := by
  let y1 := Matrix.vecMul s1 A1 + z1
  let y2 := Matrix.vecMul s2 A2 + z2
  let top := Matrix.kroneckerMap (fun a b => a * b) A1
    (1 : Matrix (Fin n2) (Fin n2) (ZMod (p : ℕ)))
  let bottom := Matrix.kroneckerMap (fun a b => a * b)
    (1 : Matrix (Fin n1) (Fin n1) (ZMod (p : ℕ))) A2
  change privateTensor (p := p) y1 y2 = privateTensor (p := p) z1 z2 +
    Matrix.vecMul (signalScalar (p := p) s1 z2 y1 s2) (mixScalar (p := p) A1 A2)
  funext q
  obtain ⟨⟨i, j⟩, rfl⟩ :=
    (finProdFinEquiv : Fin n1 × Fin n2 ≃ Fin (n1 * n2)).surjective q
  have hTop :
      dotProduct (fun u : Fin 2 × Fin n2 => s1 u.1 * z2 u.2)
        (fun u => top u (i, j)) = Matrix.vecMul s1 A1 i * z2 j := ?_
  swap
  · have h := congrFun (congrFun (Matrix.mul_kronecker_mul
        (fun (_ : Fin 1) k => s1 k) A1 (fun (_ : Fin 1) k => z2 k)
        (1 : Matrix (Fin n2) (Fin n2) (ZMod (p : ℕ)))) (0, 0)) (i, j)
    rw [Matrix.mul_one] at h
    simpa only [Matrix.kroneckerMap_apply, Matrix.mul_apply'] using h.symm
  have hBottom :
      dotProduct (fun u : Fin n1 × Fin 2 => y1 u.1 * s2 u.2)
        (fun u => bottom u (i, j)) = y1 i * Matrix.vecMul s2 A2 j := ?_
  swap
  · have h := congrFun (congrFun (Matrix.mul_kronecker_mul
        (fun (_ : Fin 1) k => y1 k)
        (1 : Matrix (Fin n1) (Fin n1) (ZMod (p : ℕ)))
        (fun (_ : Fin 1) k => s2 k) A2) (0, 0)) (i, j)
    rw [Matrix.mul_one] at h
    simpa only [Matrix.kroneckerMap_apply, Matrix.mul_apply'] using h.symm
  have hCross :
      Matrix.vecMul (signalScalar (p := p) s1 z2 y1 s2)
          (mixScalar (p := p) A1 A2) (finProdFinEquiv (i, j)) =
        dotProduct (fun u : Fin 2 × Fin n2 => s1 u.1 * z2 u.2)
            (fun u => top u (i, j)) +
          dotProduct (fun u : Fin n1 × Fin 2 => y1 u.1 * s2 u.2)
            (fun u => bottom u (i, j)) := ?_
  swap
  · change dotProduct (signalScalar (p := p) s1 z2 y1 s2)
        (fun k => mixScalar (p := p) A1 A2 k (finProdFinEquiv (i, j))) = _
    rw [← comp_equiv_dotProduct_comp_equiv _ _ (signalCoord n1 n2)]
    change dotProduct
      (fun u : (Fin 2 × Fin n2) ⊕ (Fin n1 × Fin 2) =>
        signalScalar (p := p) s1 z2 y1 s2 (signalCoord n1 n2 u))
      (fun u => mixScalar (p := p) A1 A2 (signalCoord n1 n2 u)
        (finProdFinEquiv (i, j))) = _
    simp only [signalScalar_eq, mixScalar_eq, Equiv.symm_apply_apply]
    change dotProduct
      (Sum.elim
        (fun u : Fin 2 × Fin n2 =>
          privateTensor (p := p) s1 z2 (finProdFinEquiv u))
        (fun u : Fin n1 × Fin 2 =>
          privateTensor (p := p) y1 s2 (finProdFinEquiv u)))
      (Sum.elim (fun u => top u (i, j)) (fun u => bottom u (i, j))) = _
    rw [sumElim_dotProduct_sumElim]
    congr 1
    · apply congrArg₂ dotProduct _ rfl
      funext u
      simp only [privateTensor_eq, Matrix.kroneckerMap_apply, Equiv.symm_apply_apply]
    · apply congrArg₂ dotProduct _ rfl
      funext u
      simp only [privateTensor_eq, Matrix.kroneckerMap_apply, Equiv.symm_apply_apply]
  simp only [privateTensor_eq, Matrix.kroneckerMap_apply, Equiv.symm_apply_apply,
    Pi.add_apply]
  rw [hCross, hTop, hBottom]
  change (Matrix.vecMul s1 A1 i + z1 i) * (Matrix.vecMul s2 A2 j + z2 j) =
    z1 i * z2 j + (Matrix.vecMul s1 A1 i * z2 j +
      (Matrix.vecMul s1 A1 i + z1 i) * Matrix.vecMul s2 A2 j)
  ring
