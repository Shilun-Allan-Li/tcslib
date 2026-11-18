# Quadratic source-group cross leakage: known scalar identity

Exact live frozen header/opening prose and sketch preserved. One tactic block; no new
helper/import/runtime definition, admission, efficiency premise, or native execution.
No Lean/lake/Git command or live edit was run. Root native validation remains pending.

The proof uses ONLY existing crossLeak_eq/value_eq readers and the published source-
group pow_val_add/pow_val_neg laws after sub_eq_add_neg. These normalize the supplied
quotient g^v*(g^mu)^(-1) to g^(v-mu), where v is the same scalar quadratic value on
both sides. No dot-product/count/algebra identity is reproved.

Rule 10: no public definition body is supplied to simp/rw/unfold; every simp entry is
a published reader or theorem. R-DLOG: mu is already a supplied ZMod scalar in the
original frozen header. The proof never computes/chooses a scalar logarithm from an
arbitrary group element, and introduces no group-to-scalar runtime operation. It
works for every typed state/function/input and zero dimensions, without hypotheses
on efficiency, state reachability, invertibility, or semantic PG specialization.

Static exact APIs read:
- Wee20/QuadraticSimulator.lean:152 crossLeak_eq and :164 frozen known-value target.
- Wee20/Quadratic.lean:308 value_eq.
- Pairing/Group.lean:254 pow_val_add and :260 pow_val_neg (source group).
- Existing sub_eq_add_neg, also used by the proved Quadratic.quadratic_dec_eq
  with the corresponding target-group laws.
No mathematical obstruction found.
