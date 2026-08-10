<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitHelpers.lean :: depth2OrToDNF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Reading a depth-2 OR-top circuit as a DNF

**Definition.** `depth2OrToDNF cs` turns the children `cs : List (Circuit n)` of
an OR gate into a `DNF n` (a list of terms, each term a list of `Literal n`).
It is `cs.flatMap` of a three-way match on each child `c`:

- `c = .lit l` — contributes the single one-literal term `[[l.toLiteral]]`;
- `c = .node true cs'` (an AND child) — contributes one term, the list of
  literal children of `cs'` collected by `filterMap`; non-literal grandchildren
  are silently dropped;
- `c = .node false cs'` (an OR child) — contributes one singleton term per
  literal grandchild, again via `filterMap`, so the nested OR is flattened into
  the top-level disjunction.

No depth hypothesis appears in the definition: it is total on every circuit, and
on deeper circuits it just discards the subtrees it cannot read as literals.
Correctness is stated separately, under an explicit depth assumption.

**Used in.** `depth2OrToDNF_eval`, which assumes
`(Circuit.node false cs).depth ≤ 2` and proves
`(depth2OrToDNF cs).eval x = (Circuit.node false cs).eval x`, and
`depth2OrToDNF_width_le`, which bounds `(depth2OrToDNF cs).width` by
`(Circuit.node false cs).maxFanin`. The AND-top mirror image is
`depth2AndToCNF`. Together they give LMN the DNF/CNF handle on depth-2
circuits that the switching lemma needs.
