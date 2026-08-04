<!-- generated-by: proofmatch informalization (not_in_text) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: dist_implies_correctable -->
<!-- origin: PhysRevA.55.900 run bbdd8e5c3949 verdict not_in_text (0.72) -->

# Erasures smaller than the distance are correctable

**Claim.** Let `S` be a submodule of `V = (Fin n → F_p) × (Fin n → F_p)` and
`E : Finset (Fin n)` an erasure set with `|E| < code_dist S`. Then `E` is
correctable for `S`: every `v ∈ S^⊥ω ⊓ V_E` already lies in `S`
(`correctable S E`).

**Proof.** Take `v ∈ sym_orth S ⊓ V_sub E` and suppose `v ∉ S`.

1. `v` is then a witness in the defining set of the distance
   `code_dist S = sInf {d | ∃ v ∈ S^⊥ω, v ∉ S ∧ wt v = d}`, so
   `code_dist S ≤ wt v` (`Nat.sInf_le`).
2. Since `v ∈ V_sub E`, every coordinate outside `E` vanishes, so
   `supp v ⊆ E` and hence `wt v ≤ |E|` (`Finset.card_le_card`).
3. Chaining gives `code_dist S ≤ wt v ≤ |E| < code_dist S` — a
   contradiction. Hence `v ∈ S`. ∎

**Used in.** `quantum_singleton_bound`
(blueprint: `ErrorCorrectingCodes/QuantumSingleton.tex`): the distance
hypothesis is converted into two disjoint correctable erasure sets of size
`d − 1` (via `exists_disjoint_finsets_card`), which feed
`two_disjoint_correctable_sets_bound_logical_dimension`. Knill–Laflamme
(Phys. Rev. A 55, 900) state the corresponding bound as Theorem V.1
(`n ≥ 4e + k`) but defer its proof and never introduce this symplectic step.
**Update:** Dehmel, *A Symplectic Proof of the Quantum Singleton Bound*
(arXiv:2602.20186, written against this formalisation), now proves this lemma
in the same form (hypothesis `|E| ≤ d − 1`, equivalent over ℕ); the blueprint
entry carries the corresponding `\proofsource{arXiv.2602.20186}` citation.
