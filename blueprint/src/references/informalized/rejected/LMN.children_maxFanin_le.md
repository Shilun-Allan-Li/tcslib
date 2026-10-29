<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RecursiveReduction.lean :: children_maxFanin_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Children inherit the parent's fan-in bound

**Claim.** Let `cs : List (Circuit n)`, `c ∈ cs`, and suppose
`(Circuit.node isAnd cs).maxFanin ≤ w`. Then `c.maxFanin ≤ w` — the same bound
`w`, with no decrement.

**Proof.**

1. `have h_node`, by `simp [Circuit.maxFanin]`, unfolds the node case to
   `max cs.length (List.foldr (fun c acc => max c.maxFanin acc) 0 cs)`;
   `rw [h_node] at hw` puts `hw` in that form.
2. `have h_foldr`: for any list `l` with `c ∈ l`,
   `c.maxFanin ≤ List.foldr (fun c acc => max c.maxFanin acc) 0 l`; by
   `intros l hl; induction l <;> aesop`.
3. `exact le_trans (h_foldr hc) (le_trans (le_max_right _ _) hw)`: the child's
   fan-in is at most the fold, the fold is at most the `max` with `cs.length`
   (`le_max_right`), and that is at most `w`.

**Remark.** Unlike `children_depth_le` and `children_size_sum_le`, fan-in is a
maximum rather than an accumulating quantity, so the bound passes down unchanged.

**Used in.** `circuit_layer_reduction`
(`TCSlib/BooleanAnalysis/LMN/CircuitLayerReduction.lean`), alongside
`children_depth_le`.
