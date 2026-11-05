<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: processClauseLits_rho_ne_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# processClauseLits never unfixes a variable of ρ₀

**Claim.** If `ρ₀ v ≠ none`, then `(processClauseLits lits path ρ₀ σ).2.1 v ≠ none`
for every `lits`, `path`, `σ`. That is, the encoder's simulated restriction `ρ₀`
only ever gains fixed variables; a variable already fixed stays fixed.

**Proof.** Induction on `lits`, generalizing `path`, `ρ₀`, `σ`.

1. `lits = []`: `processClauseLits` returns `ρ₀` unchanged, so
   `simpa [processClauseLits]` reduces to the hypothesis `hv`.
2. `lits = hd :: tl`, `path = []`: same — the output `ρ₀` is the input
   (`simpa [processClauseLits]`).
3. `lits = hd :: tl`, `path = p :: ps`: unfold with
   `simp only [processClauseLits]` and `apply ih`; the remaining obligation is
   `Function.update ρ₀ hd.1.var (some p.2) v ≠ none`. Expand with
   `Function.update_apply` and `split`: in the `hd.1.var = v` branch the value is
   `some p.2` (`simp`), otherwise it is `ρ₀ v` and `hv` applies.

**Used in.** Pervasively — eight call sites in this file (including
`encode_go_fst_nonfree`, `processClauseLits_no_target_of_rho_none`,
`processClauseLits_path_nil_of_rho_none_and_mem`,
`processClauseLits_rho_ne_none_of_mem`) plus two in `RoundTrip.lean`.
