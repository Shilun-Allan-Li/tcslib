# Correction proof relocation candidate

Native status reported by root: the explicit correction target has a clean header;
exact?% could not close it, and apply? returned only partial results (rc0). The other
two closure searches timed out at 200k heartbeats; they are NOT exhaustive no-match
results, and their separate TYPE_ONLY header checks remain with root. Neither closure
helper is proved by this invocation.

The source SHA-256 and 49-line body SHA-256 still match relocation.json exactly.
The recorded body hash excludes its terminal newline. The new helper contains exactly
that mathematical body, with ONLY mddhSlack_eq removed from the existing final rw list.
The explicit lambda is already in the target.
No finite product/counting/decay/closure theorem is re-proved or introduced.

The frozen old theorem's header and prose are copied verbatim into its wrapper artifact.
Its body is a term proof: funext(mddhSlack_eq p d) proves equality of the slack family
and explicit lambda; congrArg(SubexpSmall c) gives equality of the propositions; Eq.mpr
transports the new helper in the required direction. No public definition body is
supplied to simp/rw/unfold, and the unapplied function family is not simplified blindly.

Integration must REPLACE the old 49-line body with the term wrapper in the same change
that introduces the new helper. Retain exactly one mathematical proof body in live
source. The draft copy is a relocation artifact, not another live theorem proof.

This invocation contributes ONE tactic block (new helper) and ZERO in the old wrapper.
No Lean/lake/Git/native command or live edit was run. The helper proof is a native-check
candidate; do not claim its axiom inventory before root checks the integrated module.
The updated helper docstring describes the estimate and identifies its constant as
implementation-specific technical glue for the already documented Wee20 MDDH route.

Reuse unchanged from the existing checked proof: PolyExpr.eval_le,
subexpSmall_two_pow_neg, SubexpSmall.mul_pow/const_mul/mono, Nat.one_le_cast,
pow_le_pow_left₀, div_le_div_of_nonneg_left, and published scalar cast/ring laws.
No new import is needed beyond the approved Hardness imports.
