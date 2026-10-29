<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/GateMerge.lean :: reidx_eval_mergeGates_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Reindexing into the right half evaluates the original circuit

**Claim.** For a circuit `c : Circuit m₂` and Boolean gate values
`g₁ : Fin m₁ → Bool`, `g₂ : Fin m₂ → Bool`,
`(Circuit.reidx c (Fin.natAdd m₁)).eval (mergeGates g₁ g₂) = c.eval g₂` — the
mirror image of `reidx_eval_mergeGates_left` for the right block.

**Proof.** One line: `rw [Circuit.reidx_eval]; congr 1; ext i; simp`.

1. `Circuit.reidx_eval` rewrites the left side to
   `c.eval (mergeGates g₁ g₂ ∘ Fin.natAdd m₁)`.
2. `congr 1` plus `ext i` reduces to the pointwise gate equality, which `simp`
   closes via the `@[simp]` lemma `mergeGates_natAdd`.

**Used in.** Same as its left counterpart: staged for the `sorry`'d `cons` case
of `LMN.reduce_children` in `CircuitTreeManip.lean`; no current consumer.
