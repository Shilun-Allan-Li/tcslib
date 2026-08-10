<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: code_dist_le_n -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The code distance never exceeds the block length

**Claim.** For any submodule `S ≤ V n p`, `code_dist S ≤ n`, where
`code_dist S = sInf {d | ∃ v ∈ sym_orth S, v ∉ S ∧ wt v = d}`.

**Proof.** Write `D` for that set of achievable weights and case on whether it
is empty.

1. If `D = ∅` then `sInf D = 0` by the ℕ-`sInf` convention, and
   `Nat.zero_le n` finishes (`simpa [hD]`).
2. Otherwise pick `d₀ ∈ D`, witnessed by some `v ∈ sym_orth S` with `v ∉ S` and
   `wt v = d₀` (`Set.nonempty_iff_ne_empty`, then `rcases`).
3. `D` is bounded below by `0` (`BddBelow`, via `Nat.zero_le`), so
   `sInf D ≤ d₀` (`csInf_le`).
4. `d₀ = wt v ≤ n` by `wt_le_n`, since a support is a subset of `univ`.
5. `le_trans` chains steps 3 and 4.

**Remark.** The empty case is not vacuous bookkeeping: it is exactly the
degenerate `S = S^⊥ω` situation, where the convention `sInf ∅ = 0` is what makes
the bound hold.

**Used in.** `quantum_singleton_bound`, in the `code_dist S = d' + 1` branch, to
bound the distance before converting it into erasure sets.
