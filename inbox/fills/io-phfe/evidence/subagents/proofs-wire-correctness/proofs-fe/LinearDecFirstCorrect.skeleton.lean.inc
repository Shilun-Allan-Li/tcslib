/-- The first decryption block is the group-valued allowed input mask minus the last
coordinates of `sAT` [Wee20, §4.2, p. 10, (9)].

**Proof sketch.** Read the algorithm equations and transport the scalar actions with
`expVec_vecMul`. Apply pairing bilinearity and multiplicativity. The `sAWM` products cancel
entrywise, leaving the known-input action on the arbitrary group matrix and the `T` mask. -/
theorem decFirst_correct (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (κ : ℕ) (pp : PublicParams G κ)
    (f : Fn κ pp.orderParam) (M : Matrix (Fin (zDim.eval κ)) (Fin (n'.eval κ)) pp.group.G)
    (x : Fin (ℓ.eval κ) → ZMod pp.group.order)
    (z : Fin (zDim.eval κ) → ZMod pp.group.order)
    (a : SetupDraw G ℓ zDim κ pp) (s : EncDraw G κ pp) (t : KeyDraw G PG κ pp f) :
    decFirst G PG zDim κ pp f M
        (keyCore G PG zDim κ pp (setupCore G ℓ zDim κ pp a).2 f M t)
        (encCore G ℓ zDim κ pp (setupCore G ℓ zDim κ pp a).1 x
          (pp.group.expVec pp.generator z) s) =
      fun j => pp.group.pair pp.generator (groupVecMul z M j) *
        (pp.group.pair pp.generator pp.generator) ^
          (-(Matrix.vecMul (Matrix.vecMul s a.1) t.1 (Sum.inr j))).val := by
  have hCipher (j : Fin (n'.eval κ)) :
      pp.group.pairVec
          (encCore G ℓ zDim κ pp (setupCore G ℓ zDim κ pp a).1 x
            (pp.group.expVec pp.generator z) s).c1
          (fun k => M k j) =
        pp.group.pair pp.generator (groupVecMul z M j) *
          pp.group.pair pp.generator
            (groupVecMul (Matrix.vecMul (Matrix.vecMul s a.1) a.2.1) M j) := sorry
  have hKey (j : Fin (n'.eval κ)) :
      pp.group.pairVec
          (encCore G ℓ zDim κ pp (setupCore G ℓ zDim κ pp a).1 x
            (pp.group.expVec pp.generator z) s).c0
          (fun i => (keyCore G PG zDim κ pp (setupCore G ℓ zDim κ pp a).2 f M t).K1 i j) =
        pp.group.pair pp.generator pp.generator ^
            (Matrix.vecMul (Matrix.vecMul s a.1) t.1 (Sum.inr j)).val *
          pp.group.pair pp.generator
            (groupVecMul (Matrix.vecMul (Matrix.vecMul s a.1) a.2.1) M j) := sorry
  rw [decFirst_eq]
  funext j
  rw [hCipher j, hKey j, pp.group.pow_val_neg_GT, mul_inv_rev, ← mul_assoc,
    mul_inv_cancel_right]
