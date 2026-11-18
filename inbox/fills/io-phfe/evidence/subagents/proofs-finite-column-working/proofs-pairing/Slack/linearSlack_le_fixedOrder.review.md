# Averaged rank correction: fixed-order upper bound

Exact live header/opening prose preserved; one tactic block; no new helper, sampler,
probability theorem, or admission is introduced. No Lean/lake/Git command or live edit ran.

The proof uses only these existing readers/theorems:
- linearSlack_eq to expose the existing public-parameter expectation;
- ProbComp.expect_mono to average the pointwise upper bound;
- rankSlack_le_three_div for that bound;
- PublicParams.group_eq plus order_eq_of_publicParams for the scheduled modulus;
- ProbComp.expect_const to evaluate the constant upper bound.

The PublicParams.group abbreviation is read through its equation reader, not supplied
to simp as a definition body. The schedule equality acts only in a logical upper-bound
proof; no honest algorithm evaluates p or recovers group exponents.

Dependency status: rankSlack_le_three_div is an existing frozen declaration whose proof
candidate is queued at root. Both it and this averaged wrapper require root native checks
before any standard-axiom-only/admission-free claim. No mathematical obstruction found.
