<!-- generated-by: proofmatch informalization (not_in_text) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/CanonicalDTree.lean :: dtDepth_restrictFn_le_numFree -->
<!-- origin: switching-lemma run b5e074215b9e verdict not_in_text (0.72) -->

# A restricted function has decision-tree depth at most its free-variable count

**Claim.** For any `f : (Fin n → Bool) → Bool` and any restriction
`ρ : Restriction n` (a partial assignment `Fin n → Option Bool`),
`dtDepth (restrictFn f ρ) ≤ ρ.numFree`, where `restrictFn f ρ x = f (ρ.extend x)`
and `ρ.numFree` is the number of coordinates `ρ` leaves unfixed.

**Proof.** It suffices to show, for every `k`, that any `ρ` with
`ρ.numFree ≤ k` admits a decision tree of depth `≤ k` computing
`restrictFn f ρ`; applying this at `k = ρ.numFree` and feeding the result to
`depth_ge_dtDepth` gives the bound. Induction on `k`.

- *Base `k = 0`.* Then `ρ.freeVars = ∅` (`Finset.card_eq_zero`), so every
  coordinate is fixed and `ρ.extend x` does not depend on `x`. Take the leaf
  `.leaf (f (ρ.extend (fun _ => false)))`; `funext` plus a case split on `ρ i`
  shows it agrees with `restrictFn f ρ` everywhere.
- *Step `k+1`, `ρ.freeVars` nonempty.* Pick a free `v`. Fixing it in either
  direction strictly drops the count (`numFree_update_lt`), so both
  `Function.update ρ v (some false)` and `... (some true)` satisfy the
  induction hypothesis at `k`, yielding trees `T0, T1` of depth `≤ k`. Return
  `.branch v T0 T1`: its depth is `≤ k+1` by `DecisionTree.depth` and `omega`,
  and correctness follows by casing on `x v` and rewriting with
  `extend_update_self` (extending the updated restriction matches extending
  `ρ` when `x v` already has the fixed value).
- *Step `k+1`, no free variables.* Then `ρ.numFree = 0 ≤ k`, so the induction
  hypothesis applies directly and the tree's depth bound weakens by
  `Nat.le_succ`.

**Why it matters.** This is the "no restriction is worse than its own free
variables" bound: `bad_filter_empty_of_d_ge_s` uses it to show that when
`d ≥ s` there are no bad `s`-restrictions at all, which is the base case of the
switching-lemma counting argument.
