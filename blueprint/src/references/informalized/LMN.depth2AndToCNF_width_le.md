<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitHelpers.lean :: depth2AndToCNF_width_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The CNF of a depth-2 AND-top circuit has width at most the fan-in

**Claim.** For `cs : List (Circuit n)` with `(Circuit.node true cs).depth ≤ 2`,
`CNF.width (depth2AndToCNF cs) ≤ (Circuit.node true cs).maxFanin`.

**Proof.** Bound the length of every clause produced by `depth2AndToCNF`, then
take the max.

1. Each child's fan-in is dominated: `c ∈ cs → c.maxFanin ≤ (node true cs).maxFanin`,
   from a `foldr max` membership auxiliary (`induction l <;> aesop`) and
   `le_max_right` after `simp only [Circuit.maxFanin]`.
2. Per child, the clause length contributed is `1` for `.lit l`, `cs'.length`
   for an OR child `.node false cs'` (its literal children become one clause),
   and `1` for `.node true cs'` (each literal child becomes a singleton
   clause); each is `≤ (node true cs).maxFanin`. The `.lit` case uses
   `List.length_pos_iff` (as `c ∈ cs`, `cs` is nonempty and
   `maxFanin ≥ cs.length ≥ 1`); the node cases are `grind`.
3. Lift to every clause of the `flatMap` (`grind +splitImp`) — `filterMap` can
   only shorten the OR-child clause.
4. Conclude with the `foldr max 0` bound `(∀ x ∈ l, x ≤ B) → l.foldr max 0 ≤ B`
   and `convert`, unpacking the mapped list via `List.mem_map.mp`.

**Note.** The depth hypothesis `hd` is never used: non-literal grandchildren are
discarded by the `filterMap`s, so the bound holds for arbitrary `cs`. It is kept
for symmetry with `depth2AndToCNF_eval`, where depth is essential.

**Used in.** `depth2_circuit_switching_bound` (`CircuitLayerReduction.lean`),
feeding the width hypothesis of `switching_bernoulli_dtDepth_cnf_general`.
