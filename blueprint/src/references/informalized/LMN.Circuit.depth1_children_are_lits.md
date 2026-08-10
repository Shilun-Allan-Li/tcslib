<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitTreeManip.lean :: Circuit.depth1_children_are_lits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Children of a depth-≤-1 node have depth 0

**Claim.** If `(Circuit.node isAnd cs).depth ≤ 1` then every `c ∈ cs` satisfies
`c.depth = 0`.

**Proof.** Fix `c ∈ cs`.

1. Unfolding `Circuit.depth` turns the hypothesis into
   `1 + cs.foldr (fun c acc => max c.depth acc) 0 ≤ 1` (`simp [Circuit.depth] at h`),
   whence the fold is `0` (`omega`).
2. The fold dominates each member: by `induction cs`, in the `cons` case
   `List.mem_cons.mp hc` splits into the head (`le_max_left`) and the tail
   (`le_trans` with the inductive hypothesis and `le_max_right`). The `nil` case
   is vacuous since `c ∈ []` (`simp at hc`).
3. Combining `c.depth ≤ 0` gives `c.depth = 0` (`omega`).

**Remark.** The `max`-fold is spelled out rather than routed through
`Circuit.maxDepth`, so the bound has to be re-derived by induction here.

**Used in.** `Circuit.depth1_all_lits`, which composes it with
`Circuit.depth0_is_lit`.
