<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: processClauseLits_sigma_indep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Three of processClauseLits' four outputs ignore σ

**Claim.** For any `lits`, `path`, `ρ₀` and any two restrictions `σ₁ σ₂`, the
remaining path (`.1`), the updated ρ₀ (`.2.1`) and the aux block (`.2.2.2`) of
`processClauseLits lits path ρ₀ σᵢ` are equal for `σ₁` and `σ₂`. Only the
σ-component `.2.2.1` can depend on the incoming σ.

**Proof.** `induction lits generalizing path ρ₀ σ₁ σ₂`, proving the conjunction.

1. `lits = []` and `lits = hd :: tl` with `path = []` — both defining equations
   return `path`/`ρ₀` and the empty aux list, none mentioning σ
   (`simp [processClauseLits]`).
2. `lits = hd :: tl`, `path = p :: ps` — unfold one step
   (`simp only [processClauseLits]`). The recursive call's ρ₀ argument is
   `Function.update ρ₀ hd.1.var (some p.2)`, identical on both sides; only its σ
   argument differs.
3. `obtain ⟨h1, h2, h3⟩ := ih ps _ _ _` supplies the three tail equalities.
   The first two transfer verbatim; the aux component gets `(hd.2, p.2)` consed
   on, so it closes by `congrArg _ h3`. Conclude with `exact ⟨h1, h2, congrArg _ h3⟩`. ∎

**Why it matters.** This is what lets the encoder's aux output and its branching
restriction be reasoned about without tracking γ: it feeds
`encode_go_snd_sigma_indep` and `encode_go_fst_sigma_indep_at_free` (same file),
the σ-independence lemmas for `razborovEncode.go`.
