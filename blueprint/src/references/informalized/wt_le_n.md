<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: wt_le_n -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Every vector has weight at most `n`

**Claim.** For every `v : V n p`, `wt v ≤ n`, where `wt v = (supp v).card` and
`supp v = {i | v.1 i ≠ 0 ∨ v.2 i ≠ 0}` as a `Finset (Fin n)`.

**Proof.**
1. `unfold wt` turns the goal into `(supp v).card ≤ n`.
2. `supp v ⊆ (Finset.univ : Finset (Fin n))` holds trivially — every index is in
   `Finset.univ` (`Finset.mem_univ`).
3. `Finset.card_mono` gives `(supp v).card ≤ (Finset.univ).card`, and
   `simpa [Finset.card_univ]` rewrites the right side to `n`.

Purely a bookkeeping bound: supports are subsets of the `n` coordinates, and
the two `F p` components share a single index set.

**Used in.** `code_dist_le_n`, to bound the witness weight `d0` by `n` before
combining with `csInf_le`.
