<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/CanonicalDTree.lean :: termSubTree_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# `termSubTree` evaluates through to its continuation

**Claim.** For any literal list `lits`, restriction `ρ`, continuation
`cont : Restriction n → DecisionTree n` and input `x : Fin n → Bool`,
`(termSubTree lits ρ cont).eval x` equals `(cont ρ_x).eval x`, where `ρ_x` is the
left fold of `lits` over `ρ` that fixes each literal's variable to `x l.var`
whenever that variable is still free (and leaves `ρ` alone otherwise). So
following the input `x` down the sub-tree lands exactly in the leaf whose
continuation is called on that folded restriction. `private`.

**Proof.** Induction on `lits`, generalizing `ρ`.

1. `nil`: `termSubTree [] ρ cont = cont ρ` and the fold is `ρ` —
   `simp [termSubTree]`.
2. `cons l rest`: unfold `termSubTree` and `split` on the guard
   `l.var ∈ ρ.freeVars`.
   - Free: the tree is a `.branch l.var _ _`; unfold `DecisionTree.eval` and
     `cases hxv : x l.var`, so `simp [hxv, ih]` selects the child built from
     `Function.update ρ l.var (some (x l.var))` — precisely the fold's step at
     `l`. The leftover `congr 1 <;> simp [hfree]` discharges the guard.
   - Not free: `rw [ih]`, then `simp [List.foldl, hnfree]` shows the fold's step
     at `l` is the identity, so both sides use the same restriction.

**Used in.** `canonicalDTree_go_correct`, to replace the sub-tree by its
continuation before recursing on the shrunken restriction.
