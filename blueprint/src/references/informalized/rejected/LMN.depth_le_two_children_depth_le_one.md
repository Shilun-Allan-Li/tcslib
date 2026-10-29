<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitHelpers.lean :: depth_le_two_children_depth_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Children of a depth-≤-2 gate have depth ≤ 1

**Claim.** Let `cs : List (Circuit n)` and `isAnd : Bool`. If
`(Circuit.node isAnd cs).depth ≤ 2` then `c.depth ≤ 1` for every `c ∈ cs`. As in
the depth-≤-1 version, the gate type plays no role.

**Proof.** One line: `induction' cs with c cs ih <;> simp_all +arith +decide [Circuit.depth]`.
Unfolding `Circuit.depth (.node isAnd (c :: cs)) = 1 + max c.depth (foldr max 0 cs)`
turns the hypothesis into `max c.depth (…) ≤ 1`, from which the head bound is
immediate and the tail bound is the induction hypothesis; `simp_all +arith`
does both arithmetic steps.

**Used in.** `depth2OrToDNF_eval` and `depth2AndToCNF_eval` (the depth-≤-2
translation lemmas), where it is fed to `depth_le_one_children_are_lits` to show
each grandchild is a literal. A deliberately granular one-step helper: its only
content is peeling one `1 +` off the depth recursion.
