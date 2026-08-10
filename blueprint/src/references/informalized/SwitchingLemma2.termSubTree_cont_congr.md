<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/CanonicalDTree.lean :: termSubTree_cont_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# termSubTree is extensional in its continuation

**Claim.** For all `lits : List (Literal n)`, `ρ : Restriction n` and
continuations `cont₁, cont₂ : Restriction n → DecisionTree n`: if
`cont₁ ρ' = cont₂ ρ'` for every `ρ'` with `ρ'.numFree ≤ ρ.numFree`, then
`termSubTree lits ρ cont₁ = termSubTree lits ρ cont₂`. This is a `private`
helper, stated by structural recursion on `lits` (equation-compiler style, so
the recursive calls are the induction hypotheses).

**Proof.** Recursion on `lits`.

1. **`lits = []`.** Both sides reduce to `cont₁ ρ`, resp. `cont₂ ρ`, and the
   hypothesis applies at `ρ'  = ρ` with `le_refl`.
2. **`lits = l :: rest`, `l.var` free in `ρ`.** Unfold to a `.branch` on
   `l.var` (`simp only [termSubTree, hfree, ↓reduceIte]`) and match the two
   children (`congr 1`). Each child is a recursive call on `rest` at
   `Function.update ρ l.var (some false)`, resp. `(some true)`; the agreement
   hypothesis transports because fixing a variable cannot increase `numFree`
   (`numFree_update_le`, composed with `le_trans`).
3. **`lits = l :: rest`, `l.var` not free.** `termSubTree` skips `l` and the
   recursive call applies with the unchanged `ρ` and the unchanged hypothesis. ∎

**Remark.** Only `≤` is available here because a non-free head literal leaves
`ρ` — and hence `numFree` — untouched; the strict variant needs the extra
hypothesis that some literal *is* free (`termSubTree_cont_congr_strict`).
