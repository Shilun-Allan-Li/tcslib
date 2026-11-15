# Explicit-unfold scan review

The initial conservative scan collected every identifier inside rewrite arguments. It
therefore flagged ordinary data terms inside public theorem applications (Fin.append,
List.ofFn, Equiv.prodComm, and the frozen Yao index constructors), plus unrelated field
homonyms from Lean internals. Those were not definitions passed as rewrite rules.
The initial verdict and scanner versions are retained.

The corrected parser reads balanced top-level rule heads, including Unicode tuple brackets.
The actual Lean metadata query contains a superset of every required head; the exact queried
source and output are retained, and query-superset-check.txt verifies coverage. Eight
unqualified head sites were reviewed against their local proof binders in
reviewed-local-heads.json (h and hw); they shadow the unrelated imported field names.
All remaining matched definitions are own-file definitions or local aliases. There are
zero unresolved ambiguous heads and zero foreign-definition violations, including Core
and Mathlib. Kernel rfl/decide reductions are permitted by policy.md; no foreign definition
is explicitly supplied to simp/rw/dsimp/unfold. Whole-file A seals separately verify the
TCSlib implicit-reduction boundary.
