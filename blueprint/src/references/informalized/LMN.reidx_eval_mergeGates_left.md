<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/GateMerge.lean :: reidx_eval_mergeGates_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Reindexing into the left half evaluates the original circuit

**Claim.** For a circuit `c : Circuit m₁` and Boolean gate values
`g₁ : Fin m₁ → Bool`, `g₂ : Fin m₂ → Bool`,
`(Circuit.reidx c (Fin.castAdd m₂)).eval (mergeGates g₁ g₂) = c.eval g₁`. That
is, pushing `c`'s gate indices into the left block of a merged array and
evaluating there agrees with evaluating `c` against `g₁` directly.

**Proof.** One line: `rw [Circuit.reidx_eval]; congr 1; ext i; simp`.

1. `Circuit.reidx_eval` turns the left side into
   `c.eval (mergeGates g₁ g₂ ∘ Fin.castAdd m₂)`.
2. `congr 1` reduces the goal to equality of the two gate-value functions, `ext i`
   makes it pointwise, and `simp` closes it by the `@[simp]` projection lemma
   `mergeGates_castAdd`.

**Used in.** Intended for the gate-merging step of `LMN.reduce_children`
(`CircuitTreeManip.lean`), whose `cons` case is still `sorry`; nothing currently
cites it.
