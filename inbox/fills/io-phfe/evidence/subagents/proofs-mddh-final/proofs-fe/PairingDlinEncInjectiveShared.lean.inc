/-- Public challenge encoding is injective; in particular two generator coin strings yielding
one public description do not create distinct encoded objects. Serialization glue.

**Proof sketch.** Decode the description by `pairEncode_injective`, substitute equal
descriptions, then use the same pairing reader on the remaining six encodings. Apply
`List.ofFn_injective` and the group's `encG_injective`; proof irrelevance removes the
reachability and nonidentity witnesses of the shared public parameters. -/
theorem dlinEnc_injective (κ : ℕ) : Function.Injective (G.dlinEnc κ) := by
  intro c₁ c₂ h
  rcases c₁ with ⟨pp₁, a₁, b₁, u₁, v₁, w₁⟩
  rcases c₂ with ⟨pp₂, a₂, b₂, u₂, v₂, w₂⟩
  simp only [dlinEnc_eq, dlinStr_eq] at h
  rcases Prod.mk.inj (pairEncode_injective h) with ⟨hdesc, h₀⟩
  rcases Prod.mk.inj (pairEncode_injective h₀) with ⟨hgen, h₁⟩
  have hpp : pp₁.encode = pp₂.encode :=
    (PublicParams.encode_eq pp₁).trans
      ((congrArg₂ pairEncode hdesc hgen).trans (PublicParams.encode_eq pp₂).symm)
  have hPP : pp₁ = pp₂ := PublicParams.encode_injective hpp
  cases hPP
  rcases Prod.mk.inj (pairEncode_injective h₁) with ⟨hA, h₂⟩
  rcases Prod.mk.inj (pairEncode_injective h₂) with ⟨hB, h₃⟩
  rcases Prod.mk.inj (pairEncode_injective h₃) with ⟨hU, h₄⟩
  rcases Prod.mk.inj (pairEncode_injective h₄) with ⟨hV, hW⟩
  cases (G.group κ pp₁.description.val).encG_injective (List.ofFn_injective hA)
  cases (G.group κ pp₁.description.val).encG_injective (List.ofFn_injective hB)
  cases (G.group κ pp₁.description.val).encG_injective (List.ofFn_injective hU)
  cases (G.group κ pp₁.description.val).encG_injective (List.ofFn_injective hV)
  cases (G.group κ pp₁.description.val).encG_injective (List.ofFn_injective hW)
  rfl
