<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: toNAnd_toNOr_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Normalization at most doubles the size (both roots at once)

**Claim.** For every circuit `c : Circuit n`,
`(c.toNAnd).size ≤ 2 * c.size` and `(c.toNOr).size ≤ 2 * c.size`. The
alternation-forcing unary wrapper inserted at a mismatched gate can at most
double the node count. One conjunction, since `toNAnd` / `toNOr` are mutually
recursive.

**Proof.** Structural induction via `Circuit.ind`, with the node-case hypothesis
named `h_ind : ∀ c ∈ cs, c.toNAnd.size ≤ 2 * c.size ∧ c.toNOr.size ≤ 2 * c.size`.

1. **Literal case.** Both normalizations give a single clause, so
   `1 ≤ 2 * 1`; `simp +arith +decide [NAndCircuit.size, Circuit.size]` (and the
   `NOrCircuit` dual) closes each conjunct.
2. **Node case, matching root.** After `unfold Circuit.toNAnd Circuit.toNOr
   Circuit.size` and `cases isAnd`, the goal is a summed fold over
   `cs.map Circuit.toNAnd`. The private helper `foldr_add_map_le` (`induction'` +
   `linarith`) lifts the pointwise bound `g (h c) ≤ k * f c` to the folds; it is
   applied via `convert … using 1` with `fun c hc => h_ind c hc |>.1`, and
   `linarith` absorbs the `1 +` for the retained gate.
3. **Node case, mismatched root.** A local `h_node` first bounds
   `foldr (c.toNOr.size + ·) 0 cs ≤ 2 * foldr (c.size + ·) 0 cs` by list
   induction (`simp_all +decide [mul_add]`, `linarith`). The extra unary layer
   costs one node, absorbed by `Nat.le_succ_of_le h_node`; the leftover
   fold-shape and associativity mismatches are settled by `convert`,
   `ring`, `simp +arith [add_comm]` and `ac_rfl`.

**Used in.** Projected to `toNAnd_size_le` and `toNOr_size_le`.
