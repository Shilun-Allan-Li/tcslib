# rankSlack_nonneg proof candidate

The exact frozen declaration header and entire docstring are unchanged. The
candidate has one tactic block, no admissions and no new helper. No Lean, lake,
Git, live edit or checker was run. Native validation remains pending.

The group-order input is exactly pp.group.order_prime.two_le. Nat.le_add_right
1 1 and Nat.one_le_cast read it as the real inequality 1 <= order; zero_le_one
then supplies its nonnegativity. The only TCSlib definition is accessed through
the published rankSlack_eq reader.

one_le_pow₀ bounds each squared/cubed order below by one. The existing reciprocal
anti-monotonicity law one_div_le_one_div_of_le, with denominator baseline one,
proves the two reciprocal upper bounds; div_one normalizes that baseline. These
make the second and third factors nonnegative. one_div_nonneg/pow_nonneg and
sub_le_self bound all three factors above by one. The existing mul_le_one₀ law
is applied twice in the formula's left-associated product order. sub_nonneg.mpr
then gives the exact rank correction's nonnegativity.

No polynomial expansion, ring rederivation, approximate rank bound, new sampler
or statistical assumption is used. No source/group algorithm is unfolded, and
no stronger pointwise failure bound replaces the exact expression. There is no
dependency on the still-active endpoint expectation proof.

Root should check Nat.one_le_cast type inference and the two explicit power
ascriptions when natively validating. The direct product bounds use public
Mathlib lemmas, so no new helper probe is necessary. No mathematical obstruction
found; the argument actually holds whenever the denominator is at least one.
