<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitHelpers.lean :: depth2AndToCNF_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# depth2AndToCNF computes the same function as the circuit

**Claim.** For `cs : List (Circuit n)` with `(Circuit.node true cs).depth ≤ 2`
and any `x : Fin n → Bool`,
`CNF.eval (depth2AndToCNF cs) x = (Circuit.node true cs).eval x`. Here
`depth2AndToCNF` sends a literal child to a singleton clause, an OR child
`.node false cs'` to the single clause of its literal children, and an AND child
`.node true cs'` to one singleton clause per literal child.

**Proof.** Per-child correctness, then distribute the top-level AND.

1. `h_child`: for `c ∈ cs` with `c.depth ≤ 1`,
   `CNF.eval (depth2AndToCNF [c]) x = c.eval x`, by `rcases` on `c`:
   - `.lit l`: both sides unfold to `Literal.eval l.toLiteral x` (`Lit.toLiteral`,
     `CNF.evalClause`).
   - `.node false cs'`: depth `≤ 1` forces all children to be literals — first
     via `h_max_zero` (a zero `foldr max` of depths makes each depth zero), then
     re-packing `cs'` as `lits.map .lit`. The OR-fold of those literals equals
     the clause value by `foldr_or_lits_eq_clause_eval`, after matching the
     `filterMap` with `List.filterMap_congr`.
   - `.node true cs'`: again all children are literals (`h_foldr_pos`
     contrapositive), and an induction shows the CNF of the singleton clauses
     equals the AND-fold `List.foldr (fun c acc => c.eval x && acc) true cs'`.
2. `h_flatMap`: `CNF.eval` of the `flatMap` is
   `cs.all (fun c => CNF.eval (depth2AndToCNF [c]) x)`, since `CNF.eval` is
   `List.all` over clauses.
3. `h_all_child`: rewrite each factor by `h_child`, the required `c.depth ≤ 1`
   coming from `depth_le_two_children_depth_le_one cs true hd`. Done by list
   induction under a `suffices` that keeps membership in `cs` available.
4. `h_node_true`: `(Circuit.node true cs).eval x = cs.all (fun c => c.eval x)`
   by unfolding `Circuit.eval`. Finish with `rw [h_flatMap, h_all_child, h_node_true]`.

**Used in.** `depth2_circuit_switching_bound` (`CircuitLayerReduction.lean`),
which rewrites a depth-2 AND-top circuit into a CNF before invoking
`switching_bernoulli_dtDepth_cnf_general`. `depth2OrToDNF_eval` is the dual.
