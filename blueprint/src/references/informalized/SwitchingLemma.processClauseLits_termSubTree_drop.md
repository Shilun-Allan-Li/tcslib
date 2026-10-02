<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: processClauseLits_termSubTree_drop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Dropping a clause's free literals lands on the continuation's deep path

**Claim.** Let `t : Term n` have pairwise distinct literal variables, let `ρ₀ σ`
be restrictions, `cont : Restriction n → DecisionTree n` a continuation, and
`lits : List (Literal n × ℕ)` a list whose length equals
`(t.filter (fun l => decide (l.var ∈ ρ₀.freeVars))).length` and whose literals
agree entrywise with that filtered list. Assume `path` is a prefix of
`(termSubTree t ρ₀ cont).deepPath` with
`lits.length ≤ path.length ≤ (termSubTree t ρ₀ cont).deepPath.length`. Then
`(termSubTree t ρ₀ cont).deepPath.drop lits.length = (cont ρ').deepPath`, where
`ρ' = (processClauseLits lits path ρ₀ σ).2.1` is the restriction `ρ₀` updated by
walking `path`.

**Proof.** `induction' t generalizing ρ₀ σ cont path lits`.

1. `t = []`: `lits = []` (the `cons` case contradicts `hlits_len` by `simp`), and
   `simp [termSubTree, processClauseLits]` reduces both sides to
   `(cont ρ₀).deepPath`.
2. `t = l :: rest`, `by_cases hfree : l.var ∈ ρ₀.freeVars`:
   - **Free head.** `termSubTree_deepPath_head_free` supplies `b` with
     `deepPath = (l.var, b) :: (termSubTree rest (Function.update ρ₀ l.var (some b)) cont).deepPath`.
     `lits` must be a cons whose head literal is `l` (from `hlits_match 0` and
     `List.filter_cons`, discharged by `grind`/`simpa`), and `path` must start
     with `(l.var, b)` by the prefix hypothesis. `specialize ih` at the updated
     `ρ₀`/`σ`: distinctness comes from `List.pairwise_cons`, the length
     hypothesis from `filter_free_update_eq` (fixing `l.var` does not change
     which other literals are free), and the index-matching hypothesis from
     `List.filter_congr` on `hlits_match (k + 1)`; the three numeric side goals
     go by `grind`. Rewriting one step of `processClauseLits` closes the case.
   - **Fixed head.** `termSubTree_cons_nonfree` deletes the head from the tree
     without consuming a path entry, and `grind` finishes from the induction
     hypothesis.

**Used in.** `canonicalPath_preserve_processClauseLits` (private, same file),
which chains it with `canonicalDTree_alive_eq_termSubTree'` to show the encoder's
remaining path stays canonical for the updated restriction.
