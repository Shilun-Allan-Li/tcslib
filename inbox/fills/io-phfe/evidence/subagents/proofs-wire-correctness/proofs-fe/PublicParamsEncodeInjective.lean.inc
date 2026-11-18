/-- The encoded description and generator determine the public parameters uniquely.
Reachability and nonidentity witnesses are propositions and do not distinguish parameters
with the same public data. This is serialization glue for the public-parameter interface
[GJLS21, Definition 4.1; Wee20, Section 2.1].

**Proof sketch.** Read `encode_eq` and apply the shared pair-encoding injectivity theorem.
Substitute equality of the description words to align the dependent group types. Apply
`List.ofFn_injective` and the group's `encG_injective` to the generator words. Proof
irrelevance removes the reachability and nonidentity witnesses. -/
theorem encode_injective {G : BilinearGen} {κ : ℕ} :
    Function.Injective (PublicParams.encode (G := G) (κ := κ)) := by
  intro pp₁ pp₂ h
  rcases pp₁ with ⟨⟨word₁, hreach₁⟩, g₁, hg₁⟩
  rcases pp₂ with ⟨⟨word₂, hreach₂⟩, g₂, hg₂⟩
  simp only [encode_eq] at h
  rcases Prod.mk.inj (Turing.pairEncode_injective h) with ⟨hword, hgen⟩
  change word₁ = word₂ at hword
  subst word₂
  cases (G.group κ word₁).encG_injective (List.ofFn_injective hgen)
  rfl
