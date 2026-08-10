<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: encode_go_fst_acc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The encoder's γ ignores the accumulator

**Claim.** For all `f : DNF n`, `w`, `fuel`, `path`, `ρ₀ σ : Restriction n` and
`acc : List (ℕ × Bool)`,

```
(razborovEncode.go f w fuel path ρ₀ σ acc).1
  = (razborovEncode.go f w fuel path ρ₀ σ []).1
```

**Proof.** Immediate from `encode_go_acc`: rewriting with
`encode_go_acc f w fuel path ρ₀ σ acc` replaces the left-hand side by
`(r.1, acc ++ r.2)` with `r` the `acc = []` run, whose first component is
literally the right-hand side (`have := encode_go_acc …; rw [this]`).

**Used in.** The γ-side reasoning of the round trip — `encode_go_fst_eq_rec` in
`Switching/RoundTrip.lean`, plus `encode_go_fst_sigma_indep_at_free` and
`encode_go_not_kills_first_clause`, all of which need to strip the accumulator
before applying an accumulator-free γ lemma. A deliberately granular helper.
