<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/CanonicalDTree.lean :: termSubTree_deepPath_head_free -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The deepest path of `termSubTree` starts at a free head literal

**Claim.** If `l.var ∈ ρ.freeVars`, then there is a bit `b` with
`(termSubTree (l :: rest) ρ cont).deepPath = (l.var, b) ::
(termSubTree rest (Function.update ρ l.var (some b)) cont).deepPath`.
The statement only asserts existence of `b`; it does not say which branch is
deeper.

**Proof.**

1. `rw [termSubTree_cons_free l rest ρ cont hfree]` — the free guard makes the
   tree a `.branch l.var lo hi`, with `lo`/`hi` the recursive calls on
   `Function.update ρ l.var (some false)` / `(some true)`.
2. `simp only [DecisionTree.deepPath]` exposes its single `if hi.depth ≥ lo.depth`
   test, and `split` on it.
   - `hi.depth ≥ lo.depth`: `deepPath` emits `(l.var, true) :: hi.deepPath`, so
     take `b := true` (`rfl`).
   - otherwise: it emits `(l.var, false) :: lo.deepPath`, so `b := false`
     (`rfl`).

**Used in.** `termSubTree_deepPath_var_match`,
`termSubTree_deepPath_append`, `termSubTree_deepPath_split`, and the
corresponding `processClauseLits` deepPath argument in
`TCSlib/BooleanAnalysis/Switching.lean`.
