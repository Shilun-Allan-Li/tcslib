# Exact rank correction: negligible wrapper

The exact current live opening docstring/header is preserved; one tactic block and one
application only. No helper, sampler, negligibility proof, or new import is introduced.
The existing linearSlack_subexpSmall at c=1/2 gives the input to the EXISTING
SubexpSmall.negligible theorem. Mathlib half_pos and half_lt_self discharge positivity
and the strict upper bound without an auxiliary local proof.

Static searches read Foundations/Subexponential.lean:218 for the exact negligible API;
Mathlib/Algebra/Order/Field/Basic.lean:106 half_pos and :117-122 half_lt_self_iff/alias.
The frozen input theorem linearSlack_subexpSmall is pending root's dependency-ordered
native verification, so no standard-axiom-only claim is made yet. No mathematical
obstruction found. No Lean/lake/Git command or live edit was performed.
