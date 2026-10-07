<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitDegree.lean :: exists_poly_list_for_circuit_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The single-output distribution as a list of polynomials

**Claim.** Under the same hypotheses as `exists_poly_distribution_for_circuit_one`
(finite layers, `[Unique out]`, `hUses : F.onlyUsesGates (ACp_GateOps p)`, `ℓ : ℕ`),
there is a list `Ps : List (MvPolynomial (Fin n) (ZMod p))` with

- `0 < Ps.length`;
- `P.totalDegree ≤ circuitDegreeBound p ℓ F.depth` for every `P ∈ Ps`;
- for every Boolean input `x`,
  `(Ps.filter (fun P => P.eval (boolInput p x) ≠ ((F.eval₁ x : Fin 2) : ZMod p))).length * 2 ^ ℓ
  ≤ gateCountBefore F F.depth _ * Ps.length`.

The list carries one entry per seed, so multiplicities encode the uniform
distribution — no `Fintype` machinery is needed to state the bound.

**Proof.** `rcases exists_poly_distribution_for_circuit_one` to get
`⟨Seed, instF, instD, P, hpos, hdeg, hbad⟩`, reinstate the instances with `letI`, and
take `Ps := (Finset.univ : Finset Seed).toList.map P`.

- Length positive: `simpa using hpos`, since `Ps.length = Fintype.card Seed`.
- Degrees: `rcases List.mem_map.mp hQ with ⟨s, hs, rfl⟩` and then `hdeg s`.
- Counting: with `badQ s := (P s).eval (boolInput p x) ≠ ((F.eval₁ x : Fin 2) : ZMod p)`,
  `hlen : Ps.length = Fintype.card Seed` by `simp`, and
  `hfilter` rewrites the filtered list length as `(Finset.univ.filter badQ).card` —
  first `rw [list_filter_map_length]` (filter on polynomials becomes filter on
  seeds), then `finset_toList_filter_length_eq_card`. A three-step `calc` chains
  `hfilter`, the transported bound `hbad x`, and `rw [← hlen]` to put
  `Ps.length` back on the right.

**Remark.** No new mathematics — a presentational restatement of the previous
theorem in list form.
