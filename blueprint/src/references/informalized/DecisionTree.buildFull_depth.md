<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: buildFullDTree_depth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The full decision tree built from level k has depth at most n − k

**Claim.** For any `f : (Fin n → Bool) → Bool`, any level `k ≤ n` and any partial
assignment `acc : Fin n → Bool`, the complete tree
`buildFullDTree f k acc` — which queries variables `k, k+1, …, n−1` in order —
satisfies `(buildFullDTree f k acc).depth ≤ n - k`.

**Proof.** Well-founded recursion on `n - k` (`termination_by n - k`), after
`unfold buildFullDTree; split` on the guard `k < n`.

1. **Branch case** (`h : k < n`). The tree is
   `.branch ⟨k, h⟩ (… false) (… true)`, so `simp only [DecisionTree.depth]`
   turns the goal into `1 + max (depth lo) (depth hi) ≤ n - k`.
2. Two recursive applications of `buildFullDTree_depth` at level `k + 1` (side
   goal `k + 1 ≤ n` by `omega`), one per updated accumulator
   `Function.update acc ⟨k, h⟩ false / true`, bound each subtree by
   `n - (k + 1)`.
3. `max_le` merges them and `omega` closes the goal, using `k < n` to see
   `1 + (n - (k+1)) ≤ n - k`.
4. **Leaf case** (`¬ k < n`). The tree is `.leaf (f acc)`, whose depth is `0`;
   `simp [DecisionTree.depth]`.

**Used in.** The termination/witness bundle of `dtDepth` (same file), where it
supplies the `T.depth ≤ n` half of the `Nat.find` existence certificate for the
minimum decision-tree depth; also re-used in
`LMN/RestrictionMonotonicity.lean`. Note the `k ≤ n` hypothesis is bound as `_`
and is never used — the branch case gets the stronger `k < n` from `split`.
