<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitHelpers.lean :: depth_le_one_children_are_lits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Children of a depth-≤-1 gate are literals

**Claim.** Let `cs : List (Circuit n)` and `isAnd : Bool`. If
`(Circuit.node isAnd cs).depth ≤ 1`, then every `c ∈ cs` is a literal: there is
`l : Lit n` with `c = .lit l`. The gate type `isAnd` is irrelevant — only the
depth matters.

**Proof.** Fix `c ∈ cs`.

1. `c.depth = 0`. Since `Circuit.depth (.node isAnd cs) = 1 + cs.foldr (fun c acc => max c.depth acc) 0`,
   the hypothesis forces the `foldr`-max over `cs` to be `0`. A list induction
   (`h_foldr`, closed by `aesop`) gives `c.depth ≤ foldr max ... cs`, and
   `le_antisymm` with `Nat.zero_le` pins `c.depth = 0` (the strict case is
   discharged by `linarith` against `hd`).
2. Case on `c` (`rcases`). A `.lit` is the desired form; a `.node` has
   `depth = 1 + _ ≥ 1 ≠ 0`, so it is impossible — `simp_all [Circuit.depth]`
   closes both. ∎

**Used in.** `depth2OrToDNF_eval` and `depth2AndToCNF_eval`, composed with
`depth_le_two_children_depth_le_one`: it is what guarantees the `filterMap` in
`depth2OrToDNF`/`depth2AndToCNF` discards no grandchild, so the syntactic
translation loses no input.
