<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: toNAnd_toNOr_litCount -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Normalization preserves the literal count (both roots at once)

**Claim.** For every circuit `c : Circuit n`,
`(c.toNAnd).litCount = c.litCount` and `(c.toNOr).litCount = c.litCount`.
Normalization never duplicates or drops a literal occurrence — only gate
structure changes. Stated as one conjunction because `toNAnd` and `toNOr` are
mutually recursive.

**Proof.** `by_contra h_contra` followed by `revert h_contra` (a classical
double-negation shuffle that leaves the original goal), then structural
induction via `Circuit.ind`.

1. **Literal case.** Unfolding `Circuit.toNAnd` / `Circuit.toNOr` gives the
   singleton clause `[l]`, and `NAndCircuit.litCount` / `NOrCircuit.litCount` of
   a clause is `lits.length = 1 = Circuit.litCount (.lit l)`; `aesop` closes it.
2. **Node case, matching root.** After `cases isAnd <;> simp_all +decide` the
   goal is a fold over `cs.map Circuit.toNAnd` (resp. `toNOr`); an inner
   `induction cs <;> simp_all +decide [List.foldr]` pushes the induction
   hypothesis through each cons cell.
3. **Node case, mismatched root.** The extra unary wrapper contributes no
   literals, so `NAndCircuit.litCount` of the one-child node is just the child's
   count. Both conjuncts are then discharged by the same local helper
   `h_foldr : (∀ c ∈ cs, c.toNOr.litCount = c.litCount) → foldr … (cs.map Circuit.toNOr) = foldr … cs`
   (proved by `induction cs <;> aesop`), applied to `fun c hc => ih c hc |>.2`.

**Used in.** Projected to `toNAnd_litCount` and `toNOr_litCount`.
