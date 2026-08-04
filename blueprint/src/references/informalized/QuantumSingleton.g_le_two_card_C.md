<!-- generated-by: proofmatch informalization (not_in_text) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean :: g_le_two_card_C -->
<!-- origin: PhysRevA.55.900 run bbdd8e5c3949 verdict not_in_text (0.68) -->

# Cleaning bound: g(S, B ∪ C) ≤ 2|C| for a correctable part B

**Claim.** Let `B, C : Finset (Fin n)` be disjoint and `B` correctable for
`S` (`sym_orth S ⊓ V_B ≤ S`). Then

```
g S (B ∪ C) = dim(S^⊥ω ⊓ V_{B∪C}) − dim(S ⊓ V_{B∪C}) ≤ 2|C|.
```

**Proof.** Write `U := S_perp_M S (B ∪ C) = S^⊥ω ⊓ V_{B∪C}` and consider the
restriction-to-`C` map `r_C : U →ₗ V_C`, the composite of `r_E C` with the
inclusion `U ↪ V` (`(r_E C).comp (Submodule.subtype U)`).

1. *Kernel.* `ker r_C = U ⊓ V_B`: a vector of `U` is supported in `B ∪ C`,
   so killing its `C`-coordinates leaves exactly the vectors supported in
   `B`; disjointness of `B` and `C` gives the converse inclusion
   (`h_kernel_r_C`).
2. *Correctability absorbs the kernel.* Any `v ∈ U ⊓ V_B` lies in
   `S^⊥ω ⊓ V_B`, hence in `S` by correctability of `B` (`hB`); so
   `ker r_C ≤ U ⊓ S` (`h_S_perp_B_subset_S`).
3. *Rank–nullity.* `dim U = dim (range r_C) + dim (ker r_C)`
   (`LinearMap.finrank_range_add_finrank_ker`), so with step 2,
   `dim U ≤ dim (range r_C) + dim (U ⊓ S)` (`h_dim_U_le`).
4. *Range bound.* `range r_C ≤ V_C` and `dim V_C = 2|C|`
   (`Submodule.finrank_le`, `dim_V_sub`), so `dim (range r_C) ≤ 2|C|`.
5. *Second term.* `U ⊓ S ≤ S ⊓ V_{B∪C} = S_M S (B ∪ C)`, so
   `dim (U ⊓ S) ≤ dim (S_M S (B ∪ C))` (`Submodule.finrank_mono`).

Combining, `dim(S_perp_M) ≤ 2|C| + dim(S_M)`, i.e.
`g S (B ∪ C) ≤ 2|C|` (`Nat.sub_le_of_le_add`). ∎

**Used in.** `two_disjoint_correctable_sets_bound_logical_dimension`
(blueprint: `ErrorCorrectingCodes/QuantumSingleton.tex`), applied with the
partition `B ∪ (univ \ (A ∪ B)) = univ \ A` alongside
`g_complement_correctable`; that lemma in turn drives
`quantum_singleton_bound` (`k + 2(d−1) ≤ n`). This is the dimension-counting
half of the cleaning argument for stabilizer codes. Knill–Laflamme
(Phys. Rev. A 55, 900) state the resulting bound as Theorem V.1
(`n ≥ 4e + k`) with the proof deferred; no counterpart of the defect
quantity `g` or this count appears there.
**Update:** Dehmel, *A Symplectic Proof of the Quantum Singleton Bound*
(arXiv:2602.20186, written against this formalisation), proves the same step
as an injectivity statement on the quotient `(S^⊥∩V_D)/(S∩V_D)` — the
quotient-dimension phrasing of this rank–nullity count; the blueprint entry
carries the corresponding `\proofsource{arXiv.2602.20186}` citation.
