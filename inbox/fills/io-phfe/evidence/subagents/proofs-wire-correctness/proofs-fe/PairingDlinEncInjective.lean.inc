/-- Public challenge encoding is injective; in particular two generator coin strings yielding
one public description do not create distinct encoded objects. Serialization glue.

**Proof sketch.** Decode the description by `pairEncode_injective`, substitute equal
descriptions, then use the same pairing reader on the remaining six encodings. Apply
`List.ofFn_injective` and the group's `encG_injective`; proof irrelevance removes the
reachability and nonidentity witnesses of the shared public parameters. -/
theorem dlinEnc_injective (κ : ℕ) : Function.Injective (G.dlinEnc κ) := by
  intro c₁ c₂ h
  rcases c₁ with ⟨⟨⟨d₁, hd₁⟩, g₁, hg₁⟩, a₁, b₁, u₁, v₁, w₁⟩
  rcases c₂ with ⟨⟨⟨d₂, hd₂⟩, g₂, hg₂⟩, a₂, b₂, u₂, v₂, w₂⟩
  simp only [dlinEnc_eq, dlinStr_eq] at h
  rcases Prod.mk.inj (pairEncode_injective h) with ⟨hd, h₀⟩
  change d₁ = d₂ at hd
  subst d₂
  rcases Prod.mk.inj (pairEncode_injective h₀) with ⟨hG, h₁⟩
  rcases Prod.mk.inj (pairEncode_injective h₁) with ⟨hA, h₂⟩
  rcases Prod.mk.inj (pairEncode_injective h₂) with ⟨hB, h₃⟩
  rcases Prod.mk.inj (pairEncode_injective h₃) with ⟨hU, h₄⟩
  rcases Prod.mk.inj (pairEncode_injective h₄) with ⟨hV, hW⟩
  cases (G.group κ d₁).encG_injective (List.ofFn_injective hG)
  cases (G.group κ d₁).encG_injective (List.ofFn_injective hA)
  cases (G.group κ d₁).encG_injective (List.ofFn_injective hB)
  cases (G.group κ d₁).encG_injective (List.ofFn_injective hU)
  cases (G.group κ d₁).encG_injective (List.ofFn_injective hV)
  cases (G.group κ d₁).encG_injective (List.ofFn_injective hW)
  rfl
