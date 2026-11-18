# rankSlack_le_three_div proof candidate

The exact frozen theorem header and complete docstring are unchanged. There is
one tactic block, no admissions and no new helper. No Lean, lake, Git, live edit
or checker was run. Native validation remains pending.

The local q abbreviates only the real cast of pp.group.order. As in the preceding
nonnegativity candidate, pp.group.order_prime.two_le and Nat.one_le_cast give
1 <= q; no group algorithm or generator definition is unfolded. rankSlack_eq
is the sole public reading of the exact correction.

The published reciprocal-order comparison gives 1/q <= 1, and the more precise
existing one_div_pow_le_one_div_pow_of_le gives 1/q^2 <= 1/q and 1/q^3 <= 1/q.
The exponent bounds are the concrete Nat.le_add_right 1 1 and 1 2 instances;
no generic exponent/order theorem is re-proved. one_div_nonneg and pow_nonneg
give nonnegativity of the three reciprocal terms.

Let x=1/q, y=1/q^2, z=1/q^3 for explaining the existing algebra. The explicitly
nonnegative remainder is x*y*(1-z) + x*z + y*z. Ring normalization identifies
the exact rank loss with x+y+z minus this remainder. Combining it with y<=x
and z<=x yields the required 3/q. The one final nlinarith only call performs
this ring/linear combination from exactly those three concrete inequalities;
it assumes no unstated denominator clearing or independent statistical bound.

All needed tactics are already available: the imported Foundations.Subexponential
uses nlinarith at117/228 under the existing Slack imports. No new import is
requested. No dependency on rankSlack_nonneg is needed, so the two candidates
can be validated independently.

Root should check the natural-cast inference for q and the reciprocal-power
lemma's exponent inference in the two simpa steps. The final polynomial
certificate consists precisely of hrem + (x-y) + (x-z), so no mathematical gap
is known even if tactic normalization needs a local presentation adjustment.
No source loss is weakened: the exact formula remains the core loss, and only
this separate advertised coarse upper bound is proved.
