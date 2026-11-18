# mddh_subexpHard_of_adv_le: common-exponent candidate

Native authorization supplied by root: both lower closure TYPE_ONLY probes passed
rc0/errors0 in evidence/search/mddh-hardness-type-only/run. Earlier exact/apply searches
hit the 200k proof-search heartbeat limit; no exhaustive no-match claim is made.
The static name/shape searches and nearest public APIs remain in searches.txt.

The full 90-line declaration candidate preserves the approved header and public sketch.
It has exactly ONE tactic block and ZERO admissions. No new helper, import, runtime
definition, machine, realiser, sampler, or target is introduced. No Lean/lake/Git/native
command or live edit was run; root must check the candidate before any axiom claim.

Quantifier check:
- Read G.subexpDLIN_iff then subexpHard_iff to obtain a>0 common to every DLIN machine.
- Define eta=min(a,1)/4 and all exponent inequalities BEFORE intro D.
- The fixed PolyExpr majorant is also selected before D.
- For each D, choose ONE B from hBound; its pointwise bound holds for EVERY kappa.
- Existing SubexpSmall.mul_pow goes a -> 3eta; const_mul goes 3eta -> 2eta.
- Existing add combines the weighted DLIN advantage and beta at 2eta into eta.
- Existing mono transfers that bound to the actual MDDH advantage. Thresholds may
  depend on D/B, but eta is outside forall D, exactly as SubexpHard requires.

No beta nonnegativity hypothesis is required. The last step uses the published MDDH
advantage reader plus advantage_nonneg to remove the left absolute value, the supplied
pointwise hBound, and le_abs_self for the right scalar sum. This remains sound when
beta itself takes negative values.

Rule 10 / nearest reuse:
- Foundations.Subexponential: subexpHard_iff, SubexpSmall.mul_pow, .const_mul, .add,
  and .mono are consumed whole; no decay, threshold, or closure proof is reconstructed.
- Pairing.Linear: subexpDLIN_iff and dlinAdv_eq are the public readers used.
- MatrixDH.Defs: mddhAdv_eq is the public advantage reader used.
- Games.Advantage: advantage_nonneg supplies both advantage nonnegativity facts.
- Complexity.Randomized.PolyExpr.eval_le supplies the existing polynomial majorant.
  The local kappa>=1 scalar comparison C(kappa+1)^k <= C*2^k*kappa^k uses published
  scalar pow/cast/order laws, as the approved correction proof does. No new generic
  polynomial majorant or polynomial-times-exponential theorem is stated or proved.
- The nearest generic subexponential polynomial closure remains
  CoinSampling/Asymptotic.lean:subexpSmall_polyExpr_mul; its import is forbidden by dispatch
  and neither that lemma nor its proof is copied into this candidate.
- dsimp is applied only to the local let eta. Every project declaration rewritten by
  rw is a published equation reader. No public definition body is supplied to a tactic.

Dependencies: the candidate consumes only the approved lower Hardness imports. It does
not refer to mddhCorrection_subexpSmall, SelfReduction, reduction advice/RealizesOn,
or either admitted asymptotic consequence. The ordinary negligible helper is untouched.

Potential native repair surface is ordinary elaboration of the SubexpSmall.mono lambda
and scalar casts; no mathematical obstruction was found during the static review.
