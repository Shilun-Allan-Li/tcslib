/-- DLIN hardness implies uniform-matrix MDDH negligibility once the fixed-advice reduction
functions have machine realisers [Wee20, §2.1, p. 4].

**Proof sketch.** Choose the single advice family and its realiser. Apply
`EnsembleLemmas.negligible_polyExpr_mul` to the realiser's DLIN advantage. The explicit
correction is negligible by `mddhSlack_subexpSmall` and `SubexpSmall.negligible`; finish by
`Negligible.add` and `.mono`. -/
theorem mddhAdv_negligible (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (d ℓ : PolyExpr)
    (hpb : ∀ κ, 2 ^ κ ≤ p κ) (hR : G.MDDHRealizable p hp d ℓ)
    (h : G.DLINAssumption) (D : NUPPT) : Negligible (G.mddhAdv d ℓ D) :=
  G.mddh_negligible_of_adv_le d ℓ _ ((mddhSlack_subexpSmall p d hpb
    (half_pos zero_lt_one) (half_lt_self zero_lt_one)).negligible (half_pos zero_lt_one))
    (fun E => let ⟨ω, hω⟩ := G.mddhAdv_le p hp d ℓ E
      let ⟨B, hB⟩ := ((G.mddhRealizable_iff p hp d ℓ).mp hR) E ω
      ⟨B, hω B hB⟩) h D

