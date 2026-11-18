# Layered.translation proof candidate

The existing frozen header and entire docstring are unchanged in
Layered.translation.proof.lean.inc. It contains one tactic block and no admissions or
new helper declaration. The agent ran no Lean, lake, Git, live edit or proof checker.
Its native validation remains pending.

The substantive dependency is Layered.backward_action, whose native check is explicitly
still pending according to the lead. This draft must not be described as independently
standard-axiom-only, and its final axiom census must follow the successful backward-action
proof. No privacy theorem or sampling law is consumed, so there is no circular dependency.

## Exact reuse

At output coordinates, PartialGarbling.pgbCore_inl and pgbStarCore_inl read the two
masked blocks. Pi.sub_apply reads the pointwise draw subtraction, and Layered.shift_inr
identifies the shift with z. The public neg_sub equation turns -(t-z) into z-t.
neg_sub is generated from Mathlib Algebra/Group/Basic.inv_div:386, so no elementary
negation/subtraction argument is rederived.

At node coordinates, pgbCore_inr and pgbStarCore_inr expose the two matrix actions.
The reverse matrix_eq reader names their common matrix. Matrix.sub_vecMul
(Data/Matrix/Mul:1013) is exactly linearity in the vector argument; Matrix.vecMul_sub
would instead be linearity in the matrix and is not the appropriate law here.
Pi.sub_apply reads the resulting pointwise subtraction. backward_action identifies
the subtracted shift action with the same conditional source value that pgbStarCore
adds, and sub_add_cancel cancels it directly. No root/non-root case split or new
conditional cancellation lemma is required.

All simp entries are published readers or algebra laws, not definition bodies. The
proof does not unfold pgbCore, pgbStarCore, shift, matrix or any other TCSlib definition.
It introduces no sampler, efficiency witness, machine or group-to-scalar operation.
No additional import is needed beyond Layered's current imports. Focused source/reuse
searches are saved in Layered.translation.searches.txt.

The subtraction sign is the required t-shift C x z, exactly matching the frozen
statement. The proof remains valid at p=1 and all zero dimensions with no new
positivity, rank, nonzero or prime assumption. No mathematical obstruction found.
Privacy can consume this pointwise identity with the existing uniform-sample
reindexing law in the next invocation; no privacy proof is supplied here.
