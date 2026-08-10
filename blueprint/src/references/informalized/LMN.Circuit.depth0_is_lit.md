<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitTreeManip.lean :: Circuit.depth0_is_lit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A depth-0 circuit is a literal

**Claim.** For `c : Circuit m` with `c.depth = 0` there is a literal
`lr : Lit m` with `c = Circuit.lit lr`.

**Proof.** Case split on `c` (`cases c`).

1. `c = Circuit.lit l`: take `lr := l`, `exact ⟨l, rfl⟩`.
2. `c = Circuit.node _ _`: `Circuit.depth` of a node is `1 + …`, which cannot be
   `0`, so `simp [Circuit.depth] at h` closes the case.

**Remark.** The converse direction of `Circuit.exists_node_of_depth_ge_one`; the
two together are the only structural facts about `Circuit.depth` the LMN
depth-reduction argument uses.

**Used in.** `Circuit.depth1_all_lits` and `child_depth_le1_has_signed_dnf`.
