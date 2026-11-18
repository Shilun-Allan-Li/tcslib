/-- A machine-wise bound by a fixed polynomial times one negligible DLIN advantage plus
a common negligible correction gives negligible uniform-matrix MDDH advantage for every
machine adversary. Each chosen DLIN machine works at all security parameters.

**Proof sketch.** Read dlinAssumption_iff for the chosen machine. Reuse
EnsembleLemmas.negligible_polyExpr_mul, Negligible.add and pointwise domination through
mddhAdv_eq/advantage_nonneg. No machine or new negligible-closure theorem is constructed. -/
theorem mddh_negligible_of_adv_le (G : BilinearGen) (d ℓ : PolyExpr) (β : ℕ → ℝ)
    (hβ : Negligible β)
    (hBound : ∀ D : NUPPT, ∃ B : NUPPT, ∀ κ,
      G.mddhAdv d ℓ D κ ≤ (d.eval κ : ℝ) * G.dlinAdv B κ + β κ)
    (h : G.DLINAssumption) : ∀ D : NUPPT, Negligible (G.mddhAdv d ℓ D) := by
  intro D
  obtain ⟨B, hB⟩ := hBound D
  have hmain : Negligible (fun κ => (d.eval κ : ℝ) * G.dlinAdv B κ) :=
    EnsembleLemmas.negligible_polyExpr_mul d ((G.dlinAssumption_iff).mp h B)
  refine (hmain.add hβ).mono ⟨0, ?_⟩
  intro κ _
  have hnonneg : 0 ≤ G.mddhAdv d ℓ D κ :=
    (G.mddhAdv_eq d ℓ D κ).symm ▸ advantage_nonneg _ _
  rw [abs_of_nonneg hnonneg]
  exact (hB κ).trans (le_abs_self _)

