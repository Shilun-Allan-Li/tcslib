<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Restriction.lean :: zipIdx_filter_idx_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A recorded position in a short list is below the width bound

**Claim.** Let `t : List α`, `p : α × ℕ → Bool`, `l : α`, `idx w : ℕ`. If
`t.length ≤ w` and `(l, idx) ∈ (t.zipIdx).filter p`, then `idx < w`. Positions
surviving a filter on the index-tagged list are still genuine positions of `t`,
hence below any length bound for `t`.

**Proof.** Three steps, no induction.

1. `hmem := (List.mem_filter.mp h).1` discards the predicate and keeps
   `(l, idx) ∈ t.zipIdx`.
2. `obtain ⟨_, hidx, _⟩ := List.mem_zipIdx hmem` yields `idx < t.length` (after
   `simp at hidx`, since `zipIdx` starts at `0`).
3. `omega` combines it with `t.length ≤ w`.

**Remark.** The predicate `p` is arbitrary and never inspected — the lemma is
purely about `filter` shrinking a list of valid positions.

**Used in.** Nothing — no call site in the repository, so this lemma is currently
dead code. The analogous bound actually used downstream is the private
`processClauseLits_aux_idx_lt` in `BooleanAnalysis/Switching.lean`.
