<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/CanonicalDTree.lean :: termSubTree_cons_free -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Unfolding termSubTree at a free head literal

**Claim.** If the head literal's variable is free in `ρ`
(`hfree : l.var ∈ ρ.freeVars`), then
`termSubTree (l :: rest) ρ cont` equals
`.branch l.var (termSubTree rest (Function.update ρ l.var (some false)) cont)
(termSubTree rest (Function.update ρ l.var (some true)) cont)` —
i.e. the construction queries `l.var` and recurses on the tail in both
children, with `ρ` updated accordingly.

**Proof.** Immediate from the defining equation: `simp [termSubTree, hfree]`
selects the `then` branch of the `if l.var ∈ ρ.freeVars` test.

**Used in.** `termSubTree_deepPath_head_free`, which turns this structural
equation into a statement about `deepPath`; the pair
`termSubTree_cons_free` / `termSubTree_cons_nonfree` is the intended interface
for reasoning about `termSubTree` without unfolding its recursion by hand.
