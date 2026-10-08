<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/OneBit.lean :: finsetFin1_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The two one-bit frequencies are distinct

**Claim.** `(∅ : Finset (Fin 1)) ≠ {0}` — the empty frequency and the singleton
frequency `{0}` are different subsets of `Fin 1`.

**Proof.** `by decide` — decidable equality on `Finset (Fin 1)`.

**Used in.** `BooleanAnalysis.Hypercontractivity.expect_noiseOp_sq_one_bit`, `BooleanAnalysis.Hypercontractivity.one_bit_val_false`, `BooleanAnalysis.Hypercontractivity.one_bit_val_true` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/OneBit.lean`.
