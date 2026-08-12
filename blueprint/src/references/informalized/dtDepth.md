<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: dtDepth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Minimum decision-tree depth of a Boolean function

**Definition.** For `f : (Fin n → Bool) → Bool`, `dtDepth f : ℕ` is the least `d` for which
some decision tree of depth at most `d` computes `f`, i.e. the least `d` satisfying
`∃ T : DecisionTree n, T.depth ≤ d ∧ ∀ x, T.eval x = f x`. It is defined as a
`noncomputable def` in tactic mode: `classical` supplies decidability of the predicate and
`exact Nat.find …` takes the least witness.

**Proof (that the definition is well-formed).** `Nat.find` demands a nonempty predicate,
and the term supplied is the explicit witness `d := n`:

* the tree is `buildFullDTree f 0 (fun _ => false)`;
* its depth is at most `n - 0 = n` by `buildFullDTree_depth f 0 (Nat.zero_le n) _`;
* it computes `f` at every `x` by `buildFullDTree_eval f 0 (Nat.zero_le n) _ x`, whose
  agreement hypothesis `∀ i, i.val < 0 → acc i = x i` is vacuous and discharged by
  `omega`.

**Remark.** Because the bound is `T.depth ≤ d` rather than `T.depth = d`, the predicate is
upward closed, so `Nat.find` returns exactly the minimum achievable depth; in particular
`dtDepth f ≤ n` always.
