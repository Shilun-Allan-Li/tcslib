# Averaged rank correction: nonnegativity

Exact live header/opening prose preserved; one tactic block, no new helper or admission.
The proof rewrites only the published `linearSlack_eq` reader and directly reuses the
EXISTING `TCSlib.Cryptography.Games.ProbComp.expect_nonneg`. Its pointwise argument is
the existing frozen `rankSlack_nonneg` declaration, provisionally consumed while root
has its candidate queued for native validation. No probability/expectation law is reproved.

No Lean/lake/Git command or live edit was run. This proof candidate is not native-checked,
and no admission-free or standard-axiom-only claim is made before the pointwise lemma
and this wrapper pass root's checks. No mathematical obstruction was found.
