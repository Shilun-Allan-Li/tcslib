<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: buildFullDTree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The complete decision tree querying every variable in order

**Definition.** Given `f : (Fin n → Bool) → Bool`, a starting index `k : ℕ` and a partial
assignment `acc : Fin n → Bool`, the tree `buildFullDTree f k acc : DecisionTree n` is
defined by recursion on `n - k`:

* if `k < n`, it is `branch ⟨k, h⟩` whose two children are the recursive calls at `k + 1`
  with `acc` updated at index `k` to `false` and to `true` respectively
  (`Function.update`);
* otherwise it is `leaf (f acc)`.

So it queries variables `k, k + 1, …, n − 1` in order, in every branch, and each leaf
evaluates `f` on the assignment recorded by the queries made to reach it. Recursion is
justified by `termination_by n - k`.

**Remark.** `acc` is a total function, not a partial assignment: entries at indices `< k`
are whatever the caller supplied and are never overwritten. The companion lemmas fix this
by hypothesis — `buildFullDTree_depth` bounds the depth by `n - k`, and
`buildFullDTree_eval` shows the tree computes `f x` provided `acc` already agrees with `x`
below `k`.

**Used in.** `dtDepth`, where `buildFullDTree f 0 (fun _ => false)` is the witness making
the `Nat.find` predicate nonempty.
