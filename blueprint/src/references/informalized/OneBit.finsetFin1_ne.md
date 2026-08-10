<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/OneBit.lean :: finsetFin1_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The two one-bit frequencies are distinct

**Claim.** `(∅ : Finset (Fin 1)) ≠ {0}` — the empty frequency and the singleton
frequency `{0}` are different subsets of `Fin 1`.

**Proof.** `by decide` — decidable equality on `Finset (Fin 1)`.

**Used in.** Supplies the distinctness side condition of
`Finset.sum_pair finsetFin1_ne`, which splits a sum over `{∅, {0}}` into two
separate terms. Consumed by `one_bit_val_false`, `one_bit_val_true` and
`expect_noiseOp_sq_one_bit`; `private` and purely mechanical.
