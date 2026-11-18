# Revised MDDH slack proof using authorized primitive closures

This candidate SUPERSEDES mddhSlack_subexpSmall.proof.lean.inc and its proposed import.
Do NOT add CoinSampling.Asymptotic. Root reports dispatch items 2/3/9 restrict CoinSampling
imports to Contract/Efficiency in designated efficiency files, so the earlier proposed
CoinSampling.Asymptotic dependency was outside authorized scope. This revision has NO
new imports and references NO CoinSampling declaration.

Exact live opening prose/header preserved; one outer tactic block; no new public helper,
runtime definition, sampler, machine, realiser, or admission. No Lean/lake/Git command
or live edit was run. Native verification remains pending.

## Specialized proof route

Read the existing PolyExpr.eval_le bound for this target's d: d(kappa) <= C*(kappa+1)^k.
For kappa >= 1, the existing ordered-power and multiplication laws give its specialized
majorant C*2^k*kappa^k. No generic PolyExpr-times-exponential theorem is introduced.

Choose intermediate exponent e=(c+1)/2, strictly between c and 1, with e positive.
The EXISTING subexpSmall_two_pow_neg.mul_pow gives exponent e for kappa^k*2^(-kappa);
the EXISTING .const_mul gives exponent c for (4*C*2^k)*(kappa^k*2^(-kappa)); the EXISTING
.mono with threshold 1 proves this exact target. The remaining pointwise bound is
4/p <= 4*2^(-kappa) and multiplication by d(kappa). No decay, absorption, negligibility,
or closure result is reproved. The explicit 4*d/p loss and all zero-dimension behavior
remain exactly as frozen.

## Nearest reuse and restricted-import disclosure

The nearest existing public lemma is CoinSampling.subexpSmall_polyExpr_mul, which packages
the generic majorant and primitive closure route. It cannot be imported here under the
dispatch restriction reported above. The local elementary polynomial majorant overlaps
its majorant step and the inline Negligible.polyExpr_mul calculation; this specialized
use is explicit and required by the current scope. No replacement generic helper is added.

Only equation readers mddhSlack_eq and the public PolyExpr.eval_le theorem are used to
read TCSlib definitions. Mathlib division, cast, power, and ordered-multiplication laws
handle arithmetic. There is no security/realiser hypothesis, and no mathematical
obstruction was found.
