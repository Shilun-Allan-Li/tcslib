<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitDegree.lean :: exists_poly_distribution_for_circuit_outputs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Low-degree polynomial distribution for all outputs of an `AC⁰[p]` circuit

**Claim.** Let `F : FeedForward (Fin 2) (Fin n) out` have finite layers, finite
output type, and use only `AC⁰[p]` gates (`hUses : F.onlyUsesGates (ACp_GateOps p)`),
and let `ℓ : ℕ`. Then there are a finite nonempty seed type `Seed` (with
`DecidableEq`) and `P : Seed → out → MvPolynomial (Fin n) (ZMod p)` such that

- every `P s o` has `totalDegree ≤ circuitDegreeBound p ℓ F.depth = ((p - 1) * ℓ) ^ F.depth`;
- for every Boolean input `x`, the seeds that get *some* output wrong satisfy
  `#{s | ∃ o, (P s o).eval (boolInput p x) ≠ ((F.eval x o : Fin 2) : ZMod p)} * 2 ^ ℓ
  ≤ gateCountBefore F F.depth _ * Fintype.card Seed`.

**Proof.** `classical`, supplying `DecidableEq (F.nodes i)` by `Classical.decEq`.

1. Let `A := buildLayerFamily (p := p) F hUses ℓ F.depth (Nat.le_refl _)`, the
   `LayerPolyFamily` for the top layer, obtained by the recursion
   `inputLayerFamily` / `stepLayerFamily`; take `Seed := A.Seed`, with
   `A.card_pos` for nonemptiness.
2. `P s o := A.poly s (F.nodes_last.symm.rec o)`, transporting an output along
   `F.nodes_last : F.nodes (Fin.last F.depth) = out`. Degrees are exactly
   `A.degree s (F.nodes_last.symm.rec o)`.
3. `hsub`: the set of seeds failing at some *output* is a subset of the set of
   seeds failing at some *top-layer node*. Given `⟨o, ho⟩`, the witness is
   `F.nodes_last.symm.rec o`, and `simpa [FeedForward.eval]` identifies
   `F.eval x o` with `F.evalNode` at that node.
4. Conclude with `le_trans (Nat.mul_le_mul_right (2 ^ ℓ) (Finset.card_le_card hsub)) (A.bad x)`.

**Remark.** All the mathematical work sits in `buildLayerFamily`; this theorem only
re-indexes the top layer by `out` and repackages the bundled structure as an
existential statement.
