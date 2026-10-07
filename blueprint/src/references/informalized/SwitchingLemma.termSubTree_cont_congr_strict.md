<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/CanonicalDTree.lean :: termSubTree_cont_congr_strict -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Strict continuation extensionality for termSubTree

**Claim.** For all `lits : List (Literal n)` and `ρ : Restriction n`, assume some
literal of `lits` has its variable free in `ρ`
(`∃ l ∈ lits, l.var ∈ ρ.freeVars`). Then
`termSubTree lits ρ cont₁ = termSubTree lits ρ cont₂` already follows from the
weaker agreement `cont₁ ρ' = cont₂ ρ'` for all `ρ'` with
`ρ'.numFree < ρ.numFree` (strict, where `termSubTree_cont_congr` needs `≤`).
A `private` helper, stated by structural recursion on `lits`.

**Proof.** Recursion on `lits`.

1. **`lits = []`.** The existence hypothesis is impossible
   (`List.not_mem_nil`).
2. **`lits = l :: rest`, `l.var` free in `ρ`.** Unfold to a `.branch` on `l.var`
   (`simp only [termSubTree, hfree, ↓reduceIte]`). Each child updates `ρ` at
   `l.var`, which *strictly* decreases `numFree`
   (`numFree_update_lt ρ l.var false hfree` and the `true` analogue). So on each
   child it suffices to apply the non-strict `termSubTree_cont_congr` at the
   updated restriction: any `ρ'` with `ρ'.numFree ≤ (update ρ l.var b).numFree`
   satisfies `ρ'.numFree < ρ.numFree` (`Nat.lt_of_le_of_lt`), where `hcont`
   applies.
3. **`lits = l :: rest`, `l.var` not free.** `termSubTree` skips `l`. The
   witness supplied by the existence hypothesis cannot be `l` itself (it is not
   free), so it lies in `rest` (`List.mem_cons`), giving the smaller hypothesis
   needed for the recursive call at the unchanged `ρ`. ∎

**Used in.** `canonicalDTree_go_fuel_invariant` — this is exactly the step that
lets two different fuel values be compared under a `termSubTree`, since the
continuations only agree at restrictions strictly below `ρ.numFree`.
