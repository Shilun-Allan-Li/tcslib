/-- Master-secret encoding is injective on all typed master secrets.

**Proof sketch.** Recover the exact word and its pair blocks. Use encG_injective for public
matrix metadata and the shared modular-matrix injectivity under the group's order-width
bound for all scalar blocks. -/
theorem encMSK_injective (G : BilinearGen) (ℓ n : PolyExpr) (κ : ℕ)
    (pp : PublicParams G κ) : Function.Injective (encMSK G ℓ n κ pp) := by
  intro a b h
  have hw := congrArg List.ofFn h
  simp only [encMSK_eq] at hw
  rw [ofFn_padFin_of_length (quadraticMSK_length G ℓ n κ pp a),
    ofFn_padFin_of_length (quadraticMSK_length G ℓ n κ pp b)] at hw
  rcases a with ⟨M₁, ⟨W₁, U₁, V₁⟩⟩
  rcases b with ⟨M₂, ⟨W₂, U₂, V₂⟩⟩
  simp only [Wire.quadraticMSK_eq, Wire.linearMSK_eq] at hw
  have hwidth : pp.group.order ≤ 2 ^ G.wG.eval κ := ?_
  swap
  · simpa only [PublicParams.group_eq] using
      (IdentityBased.BB1Machine.order_le_two_pow G κ pp.description.val)
  have hp := pairEncode_injective hw
  have hM := Wire.groupMatrix_injective pp (congrArg Prod.fst hp)
  have hL := pairEncode_injective (congrArg Prod.snd hp)
  have hW := Encoding.Modular.encodeMatrix_injective (q := pp.group.order)
    (G.wG.eval κ) hwidth (congrArg Prod.fst hL)
  have hUV := pairEncode_injective (congrArg Prod.snd hL)
  have hUflat := Encoding.Modular.encodeMatrix_injective (q := pp.group.order)
    (G.wG.eval κ) hwidth (congrArg Prod.fst hUV)
  have hV := Encoding.Modular.encodeMatrix_injective (q := pp.group.order)
    (G.wG.eval κ) hwidth (congrArg Prod.snd hUV)
  have hU : U₁ = U₂ := ?_
  swap
  · funext i j
    simpa only [Equiv.symm_apply_apply] using
      (congrFun (congrFun hUflat i) (finProdFinEquiv j))
  cases hM
  cases hW
  cases hU
  cases hV
  rfl
