<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/EncodingProperties.lean :: roundtrip_base -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Round-trip base case: empty aux means the decoder returns σ

**Claim.** Given `f : DNF n`, width `w`, restrictions `ρ₀ σ σ_dec ρ₀_dec`, any
`dec_fuel`, and the hypotheses `hE : ∀ v, ρ₀ v = none → σ v = none`,
`hA : ∀ v, ρ₀ v = none → σ_dec v = σ v` and
`hC : ∀ v, ρ₀ v ≠ none → σ_dec v = σ v`, we have
`(razborovDecode.go f w dec_fuel σ_dec ρ₀_dec []).1 = σ`.

**Proof.** `cases dec_fuel`; both branches are the same two lines.

1. On an empty aux list `razborovDecode.go` returns `(σ_dec, ρ₀_dec)` immediately
   — this is its first defining equation for `fuel = 0` and for `fuel + 1` alike
   (`simp [razborovDecode.go]`). The goal becomes `σ_dec = σ`.
2. `funext v`, then `by_cases h : ρ₀ v = none`; `simp_all` closes the `none` case
   from `hA` and the other from `hC`. ∎

**Remark.** `hA` and `hC` are complementary over `ρ₀ v`, so together they already
assert `σ_dec = σ` pointwise; `hE` is carried in the signature for uniformity with
the surrounding invariant bundle but is not needed here.

**Used in.** `go_roundtrip_gen` (`Switching/RoundTrip.lean`), at both places where
the encoder's aux output is shown to be `[]` — the fuel-exhausted/short-circuit
base cases of the main round-trip induction.
