<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RecursiveReduction.lean :: children_depth_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A child of a depth-`d` node has depth at most `d − 1`

**Claim.** Let `cs : List (Circuit n)`, `c ∈ cs`, and suppose
`(Circuit.node isAnd cs).depth ≤ d`. Then `c.depth ≤ d - 1` (truncated
subtraction on `ℕ`).

**Proof.**

1. `contrapose! hd` turns the goal into: assuming `d - 1 < c.depth`, show
   `d < (Circuit.node isAnd cs).depth`.
2. `rw [Circuit.depth]` unfolds the node case to
   `1 + cs.foldr (fun c acc => max c.depth acc) 0`.
3. The auxiliary `have h_foldr` states that for any list `l` with `c ∈ l`,
   `List.foldr (fun c acc => max c.depth acc) 0 l ≥ c.depth`; proved by
   `intros l hl; induction l <;> aesop` (in the cons case the fold is a `max`
   whose left argument is the head's depth and whose right argument dominates
   by induction).
4. `grind` combines `1 + fold ≥ 1 + c.depth` with `d - 1 < c.depth` over `ℕ`.

**Remark.** Granular structural helper; the `d - 1` form is what the recursion in
`CircuitLayerReduction` needs, and truncated subtraction makes the statement
hypothesis-free at `d = 0`.

**Used in.** `circuit_layer_reduction` in
`TCSlib/BooleanAnalysis/LMN/CircuitLayerReduction.lean`, paired with
`children_maxFanin_le` to pass depth and fan-in budgets down to a child.
