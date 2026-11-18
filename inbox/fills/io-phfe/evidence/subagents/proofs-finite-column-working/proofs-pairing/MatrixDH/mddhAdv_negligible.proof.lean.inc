/-- DLIN hardness implies uniform-matrix MDDH negligibility once the fixed-advice reduction
functions have machine realisers [Wee20, §2.1, p. 4].

**Proof sketch.** Choose the single advice family and its realiser. Apply
`EnsembleLemmas.negligible_polyExpr_mul` to the realiser's DLIN advantage. The explicit
correction is negligible by `mddhSlack_subexpSmall` and `SubexpSmall.negligible`; finish by
`Negligible.add` and `.mono`. -/
theorem mddhAdv_negligible (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (d ℓ : PolyExpr)
    (hpb : ∀ κ, 2 ^ κ ≤ p κ) (hR : G.MDDHRealizable p hp d ℓ)
    (h : G.DLINAssumption) (D : NUPPT) : Negligible (G.mddhAdv d ℓ D) := by
  obtain ⟨ω, hω⟩ := G.mddhAdv_le p hp d ℓ D
  obtain ⟨B, hB⟩ := ((G.mddhRealizable_iff p hp d ℓ).mp hR) D ω
  have hmain : Negligible (fun κ => (d.eval κ : ℝ) * G.dlinAdv B κ) :=
    EnsembleLemmas.negligible_polyExpr_mul d ((G.dlinAssumption_iff).mp h B)
  have hslack : Negligible (mddhSlack p d) :=
    (mddhSlack_subexpSmall p d hpb (c := (1 : ℝ) / 2)
      (half_pos zero_lt_one) (half_lt_self zero_lt_one)).negligible (half_pos zero_lt_one)
  refine (hmain.add hslack).mono ⟨0, ?_⟩
  intro κ _
  have hnonneg : 0 ≤ G.mddhAdv d ℓ D κ := ?_
  swap
  · rw [G.mddhAdv_eq d ℓ D κ]
    exact advantage_nonneg _ _
  rw [abs_of_nonneg hnonneg]
  exact (hω B hB κ).trans (le_abs_self _)
