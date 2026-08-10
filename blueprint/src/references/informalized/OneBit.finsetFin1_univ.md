<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/OneBit.lean :: finsetFin1_univ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The one-bit frequency set has exactly two elements

**Claim.** `(Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}}`: the subsets of a
one-element index set are exactly `∅` and `{0}`, so the frequency index set of a
one-bit Fourier expansion is the two-element `Finset` `{∅, {0}}`.

**Proof.** `by decide` — both sides are decidably equal finite objects.

**Used in.** Same-file enumeration bookkeeping: it is the rewrite that turns the
universal Fourier sum `∑ S : Finset (Fin 1), …` into a two-term sum inside
`one_bit_val_false`, `one_bit_val_true` and `expect_noiseOp_sq_one_bit`, always
paired with `Finset.sum_pair finsetFin1_ne`. A `private` mechanical helper, not
a mathematical statement in its own right.
