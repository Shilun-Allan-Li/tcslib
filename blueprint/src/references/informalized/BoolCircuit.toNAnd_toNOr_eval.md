<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: toNAnd_toNOr_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Normalization preserves semantics (both roots at once)

**Claim.** For every circuit `c : Circuit n` and every assignment
`x : Fin n → Bool`, both normalizations compute the same Boolean value as `c`:
`(c.toNAnd).eval x = c.eval x` and `(c.toNOr).eval x = c.eval x`. The two
statements are proved as a single conjunction because `Circuit.toNAnd` and
`Circuit.toNOr` are mutually recursive, so neither induction closes alone.

**Proof.** Structural induction on `c` via the custom nested-inductive
principle `Circuit.ind`, which supplies `∀ c ∈ cs, motive c` in the `node` case.

1. **Literal case.** `unfold Circuit.toNAnd Circuit.toNOr` turns `.lit l` into
   the singleton clause `[l]`; unfolding `NAndCircuit.eval`, `NOrCircuit.eval`
   and `Circuit.eval` reduces both sides to `l.eval x` (`&& true` / `|| false`
   collapse), closed by `aesop`.
2. **Node case, matching root** (`isAnd = false` for `toNOr`, `isAnd = true`
   for `toNAnd`): the gate keeps its shape, so `simp +decide [*]` with the
   induction hypotheses rewrites `(cs.map Circuit.toNAnd).foldr …` termwise via
   `List.foldr_map`, then `induction cs <;> aesop` finishes the fold.
3. **Node case, mismatched root:** the normalizer wraps the gate in a one-child
   layer (`.node [NOrCircuit.node …]`). Unfolding the outer `NOrCircuit.eval` /
   `NAndCircuit.eval` collapses that unary AND/OR (`b && true = b`,
   `b || false = b`), reducing to the previous case; again a list induction with
   `aesop` matches the folds.

**Used in.** Projected to the two user-facing corollaries `toNAnd_eval` and
`toNOr_eval`.
