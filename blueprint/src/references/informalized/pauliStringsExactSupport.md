<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumHamming.lean :: pauliStringsExactSupport -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Pauli strings with a prescribed support

**Definition.** For `n : ℕ` and a finset `S : Finset (Fin n)` of qubit indices,
`pauliStringsExactSupport S : Finset (PauliString n)` is the finset of all
`n`-qubit Pauli strings whose support is *exactly* `S`. It is defined as
`Finset.filter (fun p => support p = S) Finset.univ`, i.e. the strings `p : Fin n → PauliBasis`
that are non-identity at every index of `S` and identity everywhere else
(`support p = Finset.univ.filter (fun i => p i ≠ PauliBasis.I)`).

Two remarks on the shape of the definition:

- The condition is an equality of finsets, not an inclusion, so the sets
  `pauliStringsExactSupport S` for distinct `S` are pairwise disjoint and
  partition the Pauli strings by support.
- Being a `Finset.filter` over `Finset.univ`, it is a plain decidable
  restriction of the ambient finite type; no bound on `S.card` is imposed.

**Used in.** `card_pauliStringsExactSupport`, which computes
`(pauliStringsExactSupport S).card = 3 ^ S.card` by identifying it with the
image of `mkWithSupport S` on `S → PauliNZ`; that count then feeds the
`PauliErrorsLe n t` cardinality computation behind the quantum Hamming bound.
