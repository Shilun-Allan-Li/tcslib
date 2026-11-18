# Straightforward existing polynomial combination stubs

Two unelaborated candidates are staged for existing G3_degrees and G4_degrees.
They must be checked only after their named upstream results have actual proofs:

- G3_degrees requires prgPoly_degrees, correctionPoly_degrees, and the proved Degree
  addition bounds. It combines their two degree inequalities with existing max_le.
- G4_degrees requires proved G3_degrees, Degree finite-sum and renaming bounds. It
  reads G4_eq and G4struct_eq and composes those interfaces.

A successful elaboration while those upstream constants still depend on sorryAx
would not validate the mathematics. These are dependency-ordered body candidates,
not proof claims from testing against the current M0 holes.

The generic Mathlib degree/rename APIs were identified in the Degree reuse notes;
these two snippets reuse the new public Degree wrappers after they are proved.
Only published owner equations are passed to rw. The structured-to-Fin renaming
uses the actual sum equivalence; definitional coercion to Sum.map should match the
named Degree renaming theorem. If elaboration needs it explicit, supply equivalence
parameters rather than unfold a foreign Params definition. No new import/helper or
source edit is proposed. Each body has one outer by and no nested tactic block.
