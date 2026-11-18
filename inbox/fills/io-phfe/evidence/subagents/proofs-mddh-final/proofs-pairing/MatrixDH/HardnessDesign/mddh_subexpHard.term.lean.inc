/-- Subexponential DLIN implies subexponential MDDH for every fixed polynomial dimension
pair, under reduction realisability [Wee20, §2.1, p. 4; JLS26, §1.1, p. 3].

**Proof sketch.** Take a smaller positive exponent than the shared DLIN exponent and one.
The fixed polynomial hybrid factor is absorbed by `.mul_pow`, `.const_mul` and `.mono`.
Combine with `mddhSlack_subexpSmall` through `.add`; the exponent is independent of `D`. -/
theorem mddh_subexpHard (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (d ℓ : PolyExpr)
    (hpb : ∀ κ, 2 ^ κ ≤ p κ) (hR : G.MDDHRealizable p hp d ℓ)
    (h : G.SubexpDLIN) : SubexpHard (G.mddhAdv d ℓ) :=
  G.mddh_subexpHard_of_adv_le d ℓ _ (fun c hc₀ hc₁ =>
    mddhSlack_subexpSmall p d hpb (c := c) hc₀ hc₁)
    (fun D => let ⟨ω, hω⟩ := G.mddhAdv_le p hp d ℓ D
      let ⟨B, hB⟩ := ((G.mddhRealizable_iff p hp d ℓ).mp hR) D ω
      ⟨B, hω B hB⟩) h

