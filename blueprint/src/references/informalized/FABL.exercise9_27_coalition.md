<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.exercise9_27_coalition -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Large coalitional influence set

**Claim.** Under the stated monotonicity and variance hypotheses, there is a coordinate set whose coalitional influence is at least $1-\epsilon$ and whose size satisfies the displayed logarithmic bound.

**Proof.** First apply the positive-bribing result to $f$, obtaining $J_+$ whose forced-$+1$ mean is at least $1-\epsilon$ and whose size is at most the stated bound (`exercise9_27_positive`). Next pass to the dual function. It remains monotone (`monotone_dualBooleanFunction`) and has the same variance (`variance_dualBooleanFunction`), so the same result supplies $J_-$ for the dual. The dual-to-original mean identity (`mean_bribeFunction_dual_one`) turns this into an upper bound $-1+\epsilon$ on the original function's mean after bribing $J_-$ to $-1$. Set $J=J_+\cup J_-$. Monotonicity of the bribed means under enlarging the forced coordinate set (`mean_bribeFunction_mono_set_one` and `mean_bribeFunction_mono_set_neg_one`) preserves the lower and upper mean bounds on $J$. The coalitional influence decomposes as the sum of the influences toward the two outputs (`coalitionalInfluence_eq_toward_add_toward`); the identities expressing those two terms as mean changes (`coalitionalInfluenceToward_one_eq_mean_change` and `coalitionalInfluenceToward_neg_one_eq_mean_change`) therefore give influence at least $((1-\epsilon)-(-1+\epsilon))/2=1-\epsilon$. Finally, the size of a union is at most the sum of the sizes, so adding the two individual bounds gives the claimed bound for $J$.

**Key facts.** `FABL.exercise9_27_positive`, `FABL.monotone_dualBooleanFunction`, `FABL.variance_dualBooleanFunction`, `FABL.mean_bribeFunction_dual_one`, `FABL.mean_bribeFunction_mono_set_one`, `FABL.mean_bribeFunction_mono_set_neg_one`, `FABL.coalitionalInfluence_eq_toward_add_toward`, `FABL.coalitionalInfluenceToward_one_eq_mean_change`, `FABL.coalitionalInfluenceToward_neg_one_eq_mean_change`.
