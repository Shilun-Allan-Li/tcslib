<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumHamming.lean :: finrank_Hn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The `n`-qubit space has dimension `2^n`

**Claim.** `Module.finrank ℂ (Hn n) = 2 ^ n`, where
`Hn n = EuclideanSpace ℂ (Fin n → Fin 2)` is the `n`-qubit Hilbert space.

**Proof.** One line: `classical; simp [Hn, finrank_euclideanSpace,
Fintype.card_fin]`.

- `finrank_euclideanSpace` gives `finrank ℂ (EuclideanSpace ℂ ι) =
  Fintype.card ι`.
- The index type is `Fin n → Fin 2`, whose cardinality `simp` computes as
  `(Fintype.card (Fin 2)) ^ (Fintype.card (Fin n)) = 2 ^ n` via
  `Fintype.card_fin`.

**Used in.** `quantum_hamming_bound_raw`: combined with
`Submodule.finrank_le (ErrorSphere n t C)` it turns the abstract bound
`finrank (ErrorSphere n t C) ≤ finrank (Hn n)` into the numeric `≤ 2 ^ n` that
is the right-hand side of the quantum Hamming bound.
