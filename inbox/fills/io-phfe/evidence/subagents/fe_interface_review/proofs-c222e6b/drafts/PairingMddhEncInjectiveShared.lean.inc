/-- Matrix-challenge encoding is injective on reachable public challenges. Serialization glue.

**Proof sketch.** Use `pairEncode_injective` to separate public parameters and matrix words.
Read the shared public encoding and apply `encG_injective` to its generator; description
reachability witnesses are propositions. Then use `groupMatrixEnc_injective` twice. -/
theorem mddhEnc_injective (d ℓ : PolyExpr) (κ : ℕ) :
    Function.Injective (G.mddhEnc d ℓ κ) := by
  intro c₁ c₂ h
  rcases c₁ with ⟨pp₁, M₁, R₁⟩
  rcases c₂ with ⟨pp₂, M₂, R₂⟩
  simp only [mddhEnc_eq] at h
  rcases Prod.mk.inj (pairEncode_injective h) with ⟨hpp, hmat⟩
  have hPP : pp₁ = pp₂ := PublicParams.encode_injective hpp
  cases hPP
  rcases Prod.mk.inj (pairEncode_injective hmat) with ⟨hM, hR⟩
  cases (G.group κ pp₁.description.val).groupMatrixEnc_injective hM
  cases (G.group κ pp₁.description.val).groupMatrixEnc_injective hR
  rfl
