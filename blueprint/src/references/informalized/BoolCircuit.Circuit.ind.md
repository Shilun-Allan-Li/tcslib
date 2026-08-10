<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/Circuit.lean :: Circuit.ind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Induction principle for circuit trees

**Claim.** Let `motive : Circuit n → Prop`. If `motive` holds of every leaf
`.lit l`, and for every gate `node isAnd cs` it holds of `.node isAnd cs`
whenever it holds of *all* children (`∀ c ∈ cs, motive c`), then `motive c`
holds for every circuit `c`.

**Proof.** This is a repackaging of the auto-generated recursor, not a new
mathematical fact.

1. Apply `Circuit.rec` with the list-level motive instantiated as
   `fun cs => ∀ c ∈ cs, motive c` — this is the step that converts the nested
   inductive's auxiliary `List (Circuit n)` motive into a membership statement.
2. The `lit` and `node` cases are `hlit` and `hnode` verbatim.
3. The `nil` case is `fun _ h => nomatch h` (no member of `[]`).
4. The `cons` case does `cases hc` on the membership proof: `head` gives
   `ih_head`, `tail _ h` gives `ih_tail c h`.

**Used in.** The standard induction driver for `Circuit` throughout the
library, e.g. `induction' c using Circuit.ind with l isAnd cs ih` in
`Switching/Circuit.lean` and `LMN/CircuitReindex.lean`; Lean's `induction`
cannot recurse through the nested `List (Circuit n)` argument directly.
