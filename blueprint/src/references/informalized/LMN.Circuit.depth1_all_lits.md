<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitTreeManip.lean :: Circuit.depth1_all_lits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Children of a depth-≤-1 node are literals

**Claim.** If `(Circuit.node isAnd cs).depth ≤ 1` then every `c ∈ cs` is a
literal circuit: `∃ lr : Lit m, c = Circuit.lit lr`.

**Proof.** One line: introduce `c` and `hc : c ∈ cs`, then
`exact Circuit.depth0_is_lit c (Circuit.depth1_children_are_lits isAnd cs h c hc)`
— the depth bound gives `c.depth = 0`, and depth 0 gives a literal.

**Remark.** A convenience composition, not new content: it packages the two
granular helpers into the exact shape (`∃ lr, c = Circuit.lit lr`) that the
compression lemmas expect, so callers never have to mention depth 0.

**Used in.** `absorbOneLevel_depth1` and `child_depth_le1_has_signed_dnf`,
where it supplies the all-literal-children hypothesis of
`and_of_lit_children_cnf` and `or_of_lit_children_dnf`.
