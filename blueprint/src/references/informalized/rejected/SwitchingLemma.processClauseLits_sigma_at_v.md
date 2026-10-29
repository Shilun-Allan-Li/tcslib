<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: processClauseLits_sigma_at_v -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The output σ at v depends only on the input σ at v

**Claim.** For any `lits`, `path`, `ρ₀`, restrictions `σ₁ σ₂` and a variable `v`
with `σ₁ v = σ₂ v`, the σ-components agree at `v`:
`(processClauseLits lits path ρ₀ σ₁).2.2.1 v = (processClauseLits lits path ρ₀ σ₂).2.2.1 v`.
A pointwise refinement of σ-independence: `processClauseLits` never reads σ at
one variable to decide σ at another.

**Proof.** `induction lits generalizing path ρ₀ σ₁ σ₂`.

1. `lits = []`, and `lits = hd :: tl` with `path = []` — both return the input σ,
   so the goal is `hv` itself (`simp [processClauseLits, hv]`).
2. `lits = hd :: tl`, `path = p :: ps` — unfold one step
   (`simp only [processClauseLits]`) and `apply ih`. The remaining obligation is
   that the two updated σ's agree at `v`:
   `Function.update σ₁ hd.1.var (some (!hd.1.neg)) v = Function.update σ₂ … v`.
3. `simp only [Function.update_apply]` then `split_ifs <;> [rfl; exact hv]`: if
   `v = hd.1.var` both sides are the same written value `some (!hd.1.neg)`
   (independent of σ); otherwise both are unchanged and `hv` applies. ∎

**Used in.** `encode_go_fst_sigma_indep_at_free` (same file), in the branch where
`v` has become fixed by the updated `ρ₀` — there the encoder's γ at `v` is read
off `processClauseLits` directly, and this lemma equates the two σ-instantiations.
