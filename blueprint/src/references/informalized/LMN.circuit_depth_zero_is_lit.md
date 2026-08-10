<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CompressionStep.lean :: circuit_depth_zero_is_lit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A depth-zero circuit is a literal

**Claim.** If `c : Circuit m` has `c.depth = 0`, then `c = Circuit.lit l` for
some literal `l : BoolCircuit.Lit m`.

`Circuit` has exactly two constructors, `lit` and `node isAnd cs`, and
`Circuit.depth` is `0` on `lit` and `1 + …` on `node`. So depth `0` rules out the
`node` case.

**Proof.** `cases c`.

1. `lit l`: take the witness `l` itself, `exact ⟨l, rfl⟩`.
2. `node isAnd cs`: `Circuit.depth (.node _ cs) = 1 + cs.foldr (max · ·) 0`, which
   can never equal `0`; `simp [Circuit.depth] at h` closes the goal from the
   contradictory hypothesis.

**Used in.** `layer2_composed_bound_base`, to turn the hypothesis
`c_top.depth + 2 ≤ 2` into a literal top gate.
