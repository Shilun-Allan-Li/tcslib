<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitDegree.lean :: exists_poly_distribution_for_circuit_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Low-degree polynomial distribution for a single-output `AC⁰[p]` circuit

**Claim.** Let `F : FeedForward (Fin 2) (Fin n) out` have finite layers, a unique
output (`[Unique out]`), and use only `AC⁰[p]` gates
(`hUses : F.onlyUsesGates (ACp_GateOps p)`), and let `ℓ : ℕ`. Then there are a
finite nonempty seed type `Seed` (with `DecidableEq`) and
`P : Seed → MvPolynomial (Fin n) (ZMod p)` with

- `(P s).totalDegree ≤ circuitDegreeBound p ℓ F.depth = ((p - 1) * ℓ) ^ F.depth` for every seed;
- for every Boolean input `x`,
  `#{s | (P s).eval (boolInput p x) ≠ ((F.eval₁ x : Fin 2) : ZMod p)} * 2 ^ ℓ
  ≤ gateCountBefore F F.depth _ * Fintype.card Seed`.

**Proof.** Same shape as `exists_poly_distribution_for_circuit_outputs`, with the
output quantifier removed. After `classical` and classical `DecidableEq` on layers:

1. `A := buildLayerFamily (p := p) F hUses ℓ F.depth (Nat.le_refl _)`; take
   `Seed := A.Seed`, nonempty by `A.card_pos`.
2. Fix the single top-layer node `outNode := F.nodes_last.symm.rec default` and set
   `P s := A.poly s outNode`; the degree bound is `A.degree s outNode`.
3. `hsub`: the bad set for `P` is contained in `A`'s bad set (witness `outNode`),
   using `simpa [FeedForward.eval₁, FeedForward.eval, outNode]` to identify
   `F.eval₁ x` with `F.evalNode outNode x`.
4. Conclude by `le_trans (Nat.mul_le_mul_right (2 ^ ℓ) (Finset.card_le_card hsub)) (A.bad x)`.

**Remark.** Since `out` is a subsingleton the inclusion in step 3 is in fact an
equality; only `⊆` is proved, which is all the counting bound needs.

**Used in.** `exists_poly_list_for_circuit_one`, its list-with-multiplicity restatement.
