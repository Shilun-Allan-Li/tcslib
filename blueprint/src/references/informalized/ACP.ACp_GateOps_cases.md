<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/ACpGates.lean :: ACp_GateOps_cases -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Case analysis on an `AC⁰[p]` gate

**Claim.** If `op ∈ ACp_GateOps p`, then `op` is one of four things:

- the identity, `⟨PUnit, fun x => x PUnit.unit⟩`;
- NOT, `⟨Fin 1, fun x => 1 - x 0⟩`;
- unbounded AND of some fan-in, `∃ n, op = ⟨Fin n, fun x => ∏ i, x i⟩`;
- unbounded `MOD p` of some fan-in, `∃ n, op = modGateOp p n`.

**Proof.** Unfold `ACp_GateOps` and `AC_GateOps` in the hypothesis, then peel the
unions.

1. `rcases h` splits the outer `AC_GateOps ∪ ⋃ n, {modGateOp p n}`.
2. In the `AC_GateOps` branch, split again: membership in the two-element set
   `{GateOp.id (Fin 2), NOT}` is turned into a disjunction of equations by
   `simp [GateOp.id]`, and `rcases ... with rfl | rfl` picks the identity or NOT
   case; membership in `⋃ n, {AND_n}` is destructured by `Set.mem_iUnion.mp`.
3. The `MOD p` branch is `Set.mem_iUnion.mp` again, giving the fan-in `n`.

**Remark.** The identity case is stated as the *unfolded* `⟨PUnit, fun x => x PUnit.unit⟩`
rather than `GateOp.id (Fin 2)`; since `GateOp.id` is an `abbrev`, the two are the
same term and `simp [GateOp.id]` is what exposes it. Nothing here is deep — the
value of the lemma is packaging a set-membership fact as a four-way `rcases`
pattern.

**Used in.** `exists_gate_poly_family` in
`RazborovSmolensky/CircuitDegree.lean:354`, as
`rcases ACp_GateOps_cases (p := p) hop with hId | hNot | hAnd | hMod` — the case
split that drives the whole gate-by-gate polynomial approximation argument.
