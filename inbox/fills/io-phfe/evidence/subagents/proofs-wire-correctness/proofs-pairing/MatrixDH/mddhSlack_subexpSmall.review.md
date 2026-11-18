# MDDH polynomial-over-order slack: candidate

Exact live opening prose/header preserved, one outer tactic block, no admissions.
No Lean/lake/Git command, live edit, realiser, machine, sampler, or new helper is supplied.
Native validation remains for root.

## Required precise import

Add `import TCSlib.Cryptography.CoinSampling.Asymptotic` when integrating. The current
SelfReduction import graph DOES NOT include it. A static import-graph traversal found
no path from this existing module back to SelfReduction, so adding this edge is cycle-free.
This is a reuse import, not a new closure theorem.

## Reuse and proof route

The EXISTING `CoinSampling.subexpSmall_polyExpr_mul` directly applies to the syntactic
polynomial `(PolyExpr.const 4).mul d` and the EXISTING `subexpSmall_two_pow_neg`. It already
packages the PolyExpr growth estimate and the shared SubexpSmall.mul_pow/const_mul/mono
proof. Re-expanding those steps here would duplicate that public closure result.

The remaining argument is pointwise domination with threshold 0: hpb casts to Real;
`div_le_div_of_nonneg_left` gives 4/p <= 4*(2 inverse)^kappa; multiplication by d(kappa)
preserves the bound. Only the `mddhSlack_eq` and PolyExpr.eval_mul/eval_const equation
readers expose public definitions. Nat.absolute cast, nonnegative division, elementary
real multiplication, and le_abs_self supply the absolute-value comparison required by
SubexpSmall.mono.

The positive target-exponent hypothesis hc0 remains unchanged; as with the existing
CoinSampling.subexpSmall_drawSlack closure, the proof only needs c < 1. No mathematical
obstruction found. No dependency on a realisability or cryptographic security theorem.
