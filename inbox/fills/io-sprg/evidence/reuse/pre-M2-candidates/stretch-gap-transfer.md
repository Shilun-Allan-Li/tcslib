# Full power-gap route for jls_hasPolyStretch

This is the exact mathematical proof plan for the existing theorem, not a checked
Lean body. It adds no hypothesis to the statement and uses no new asymptotic notion.
All constants/exponents below depend only on P, the supplied tau, and the supplied
polynomial output bound; the final threshold is independent of the prime schedule.

1. Let a=(E:Real)*D and b=(E:Real)*(delta:Real)/2. From the staged E0 strict-gap
   candidate, b>5 and E*(tau-1)>5. D>=1 gives a*(tau-1)>5. Thus
     g1 = a*(tau-1)-5 > 0, g2 = b-5 > 0.
   Set epsilon = min(g1,g2)/2 > 0. Then 2*epsilon<=g1,g2.
2. For k>=1, owner equations and existing cast/power identities give
     (n(k):Real)=k^a, and m(k)>=n(k)^tau=k^(a*tau)
   from the input BoolPRG.HasStretch reader. The staged noise-width comparison gives
     (w(k):Real)>=k^b/2.
   Also (k+1)^5<=32*k^5. Natural division is bounded by real division by the existing
   `Nat.cast_div_le`, not a local cast/rounding argument.
3. Apply the all-parameter payload estimate and the previous inequalities:
     seedBits(k) <= C1 * (k^(5+a) + m(k)*k^(5-b) + k^5)
                 <= C2 * m(k) * k^(-2*epsilon).
   The first and third terms use 5+a<=a*tau-2*epsilon and a>=0; the second uses
   5-b<=-2*epsilon. This holds for all sufficiently large k, uniformly in pi.
   Use Real.rpow_add/sub/mul, mul_rpow, rpow_natCast and exponent monotonicity.
4. Absorb the one fixed C2 by positive power growth: existing tendsto_rpow_atTop
   composed with tendsto_natCast_atTop_atTop gives eventually C2<=k^epsilon.
   Hence eventually
     S(k) := (seedBits(k):Real) <= m(k)*k^(-epsilon).
   This is ordinary power growth. Do not use/reprove a subexponential decay lemma.
5. Read the actual output polynomial bound. Existing PolyExpr.eval_le gives constants
   A,r with m(k)<=A*(k+1)^r. For k>=1 this is <=A*2^r*k^r. Positive power growth
   absorbs A*2^r into k, so for K=(r+1:Nat)>0 one gets eventually m(k)<=k^K.
   Reuse PolyExpr.eval_le; do not do induction over the syntactic polynomial.
6. Choose the explicit fixed stretch exponent
     tau' = 1 + epsilon/(2*K) > 1.
   Raise the nonnegative inequality S<=m*k^(-epsilon) to tau'. By existing mul_rpow,
   rpow_mul and m<=k^K,
     S^tau' <= m^tau' * k^(-epsilon*tau')
            = m * m^(tau'-1) * k^(-epsilon*tau')
           <= m * k^(K*(tau'-1)-epsilon*tau')
           <= m,
   since K*(tau'-1)=epsilon/2 and epsilon/2-epsilon*tau'<0. Here k>=1, m>=1
   eventually from its input stretch bound; the power/order APIs apply directly.
7. Use SPRG.Raw.hasPolyStretch_iff, select tau' and the maximum of the finitely many
   thresholds from these eventual facts, and read jlsSPRG_raw_outLen/seedBits_eq.
   The arbitrary schedule changes only p, while every length/bound is independent
   of p, so no schedule-dependent threshold was selected.

## Exact selected public APIs

All Mathlib paths below are under .lake/packages/mathlib/Mathlib/.

| API | Location | Use |
| --- | --- | --- |
| `Nat.lt_floor_add_one` | Algebra/Order/Floor/Semiring.lean:61 | E0's strict real lower bound before using hE. |
| `Real.rpow_natCast` | Analysis/SpecialFunctions/Pow/Real.lean:58 | Convert integer/natural powers to real exponent notation. |
| `Real.rpow_add`, `rpow_sub` | same file:195/:248 | Collect ordinary power factors and quotients for positive k. |
| `Real.rpow_mul`, `rpow_natCast_mul` | same file:399/:495 | Identify n(k) and the nested schedule / noise exponents. |
| `Real.mul_rpow`, `div_rpow` | same file:461/:469 | Raise products/quotients in the final transfer. |
| `Real.rpow_le_rpow` | same file:528 | Raise inequalities with nonnegative exponent. |
| `Real.rpow_le_rpow_of_exponent_le` | same file:595 | Compare exponents with base k>=1. |
| `Real.rpow_le_rpow_of_nonpos` | same file:543 | Alternative inverse-power comparison if used; not needed for the selected final tau' route. |
| `Real.rpow_le_one_of_one_le_of_nonpos` | same file:654 | Final negative exponent contributes at most one. |
| `Nat.cast_div_le` | Data/Nat/Cast/Order/Field.lean:30 | Floor natural quotient <= real quotient, including zero denominator; here width is positive. |
| `tendsto_rpow_atTop` | Analysis/SpecialFunctions/Pow/Asymptotics.lean:32 | Fixed positive powers absorb each constant. |
| `tendsto_natCast_atTop_atTop` | Order/Filter/AtTopBot/Archimedean.lean:35 | Transport real power growth along natural k. |
| `Filter.Tendsto.eventually_ge_atTop` | Order/Filter/AtTopBot/Tendsto.lean:36 | Extract the required constant threshold. |
| `Complexity.PolyExpr.eval_le` | TCSlib/Complexity/Randomized/PolyExpr.lean:159 | Output polynomial normal-form majorant. |
| `PolyExpr.eval_subst`, `eval_mono` | same file:134/:142 | Read the concrete mBound and scheduled input without foreign unfolding. |
| Shared Subexponential public API | TCSlib/Cryptography/Foundations/Subexponential.lean:132 onward | Inspected; reserve for the later advantage-decay milestone. It is not an ordinary stretch lemma. |

No exact?/apply? or Lean claim is made. Before adding any general stretch-transfer
helper, run the required overlap probes against this exact statement; the steps
above use existing generic power, polynomial-bound and filter APIs and only need
construction-specific combinations. No source statement repair appears necessary.
