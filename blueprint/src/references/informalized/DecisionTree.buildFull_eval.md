<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: buildFullDTree_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The full decision tree computes f, given an agreeing accumulator

**Claim.** Let `f : (Fin n → Bool) → Bool`, `k ≤ n`, and let `acc, x : Fin n → Bool`
agree on every coordinate already queried, i.e. `hinv : ∀ i, i.val < k → acc i = x i`.
Then `(buildFullDTree f k acc).eval x = f x`.

**Proof.** Well-founded recursion on `n - k` (`termination_by n - k`), after
`unfold buildFullDTree; split`.

1. **Branch case** (`h : k < n`). `simp only [DecisionTree.eval]` exposes the
   query `if x ⟨k, h⟩ then hi.eval x else lo.eval x`; `cases hxv : x ⟨k, h⟩`
   splits on the queried bit and `if_neg` / `if_pos` selects the matching
   subtree.
2. In each branch, apply the recursive `buildFullDTree_eval` at level `k + 1`
   (side goal `k + 1 ≤ n` by `omega`), which leaves the invariant for the
   updated accumulator `Function.update acc ⟨k, h⟩ b`.
3. Re-establish the invariant by `by_cases heq : i = ⟨k, h⟩`. At `i = ⟨k, h⟩`
   the update writes exactly `b`, which equals `x i` by `hxv`
   (`simp [Function.update, hxv]`). Otherwise the update is transparent
   (`simp only [Function.update, heq]`) and `hinv i` applies, its index bound
   coming from `i.val ≠ k` (via `Fin.ext`) plus `omega`.
4. **Leaf case** (`¬ k < n`). Every `i : Fin n` has `i.val < n ≤ k`, so `hinv`
   covers all coordinates: `funext` gives `acc = x`, and rewriting turns
   `f acc` into `f x`.

**Used in.** Together with `buildFullDTree_depth`, this is the correctness half
of the `Nat.find` witness for `dtDepth` — it is what makes the minimum
decision-tree depth of any `f` well defined (bounded by `n`).
