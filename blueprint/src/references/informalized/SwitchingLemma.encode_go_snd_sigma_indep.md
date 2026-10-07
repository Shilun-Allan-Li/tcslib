<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: encode_go_snd_sigma_indep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The aux output does not depend on the σ argument

**Claim.** For all `f : DNF n`, `w`, `fuel`, `path` and `ρ₀ σ₁ σ₂ : Restriction n`,

```
(razborovEncode.go f w fuel path ρ₀ σ₁ []).2 = (razborovEncode.go f w fuel path ρ₀ σ₂ []).2
```

The encoder's aux list is determined by `f`, `w`, the path and `ρ₀` alone; `σ`
only feeds the γ-component.

**Proof.** Induction on `fuel`, generalizing `path`, `ρ₀`, `σ₁`, `σ₂`.

1. Base cases: `fuel = 0` (`cases path <;> simp [razborovEncode.go]`) and
   `fuel + 1` with `path = []` — the aux output is the (empty) accumulator.
2. `fuel + 1`, `path = step :: rest`: `simp only [razborovEncode.go]` and `split`
   twice; the `f.find? = none` and empty-filter branches return `[]` (`rfl`).
   Note the filter and the `find?` test mention only `ρ₀`, so the two sides take
   the same branch.
3. Recursive branch `fl :: fls`: `processClauseLits_sigma_indep` gives that the
   remaining path (`hpath`), the updated `ρ₀` (`hrho`) and the emitted aux block
   (`haux_eq`) all agree between the `σ₁` and `σ₂` runs.
4. Rewrite both recursive calls with `encode_go_acc` (instances `hacc₁`, `hacc₂`)
   to expose them as `accumulator ++ (acc = [] run)`, `simp only` with
   `List.nil_append`, then `rw [haux_eq, hpath, hrho]` to align the prefixes and
   arguments, and finish with `congrArg _ (ih _ _ _ _)` on the tails.

**Used in.** `go_roundtrip_gen` (`Switching/RoundTrip.lean`), where the decoder
is run on aux produced from a different σ than the one in the invariant.
