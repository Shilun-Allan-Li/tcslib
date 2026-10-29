<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: encode_go_fst_sigma_indep_at_free -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# γ at a free variable does not depend on the initial σ

**Claim.** For all `f : DNF n`, `w`, `fuel`, `path`, `ρ₀ σ₁ σ₂ : Restriction n`
and `v : Fin n` with `ρ₀ v = none`, `σ₁ v = none` and `σ₂ v = none`,

```
(razborovEncode.go f w fuel path ρ₀ σ₁ []).1 v = (razborovEncode.go f w fuel path ρ₀ σ₂ []).1 v
```

**Proof.** Induction on `fuel`, generalizing `path`, `ρ₀`, `σ₁`, `σ₂`.

1. Base cases (`fuel = 0`, and `fuel + 1` with `path = []`): γ is the input σ, so
   both sides are `none` by `simp [razborovEncode.go, h₁, h₂]`.
2. `fuel + 1`, `path = step :: rest`: `simp only [razborovEncode.go]` and `split`
   twice; the `f.find? = none` and empty-filter branches again return the input σ
   (`simp [h₁, h₂]`).
3. Recursive branch `fl :: fls`: `processClauseLits_sigma_indep` gives that the
   remaining path (`hpath`) and updated `ρ₀` (`hrho`) agree across the two runs.
   `conv_lhs`/`conv_rhs => rw [encode_go_fst_acc]` drop the accumulators, then
   `rw [hpath, hrho]`.
4. `by_cases` on `hv : (processClauseLits (fl :: fls) (step :: rest) ρ₀ σ₂).2.1 v = none`.
   - Still free: `processClauseLits_sigma_none_of_rho_none` (with `hfree`, and
     `hrho ▸ hv` for the σ₁ run) shows the clause pass left σ at `v` equal to its
     input, hence still `none` on both sides; `exact ih _ _ _ _ hv hσ₁_eq hσ₂_eq`.
   - Now fixed: `encode_go_fst_nonfree` collapses both sides to the clause pass's
     σ at `v`, and `processClauseLits_sigma_at_v` (using `h₁`, `h₂`) equates
     those, since that output depends only on the initial σ-value at `v`.

**Used in.** `go_roundtrip_gen` (`Switching/RoundTrip.lean`), to compare the
encoder's γ against the decoder's reconstructed σ at still-free variables.
