# M2 stretch proof preparation

Snapshot inspected: `bb3455c5015031a9b03a4013fbe8d372fc09791d`, with the selected
`Mathlib.Algebra.Order.Floor.Semifield` import now added to Stretch by the lead.
No implementation source was edited by these preparers. No Lean, Lake, cache,
build, exact?, apply?, or axiom command was run. Every `.proof` is unelaborated.

No counterexample or mathematical obstruction was found for any of the four
existing Stretch obligations. The numeric payload estimate and power-gap transfer
are described completely below; only the two short transport obligations have
standalone replacement bodies. Do not treat the remaining plans as completed Lean
proofs. Every current candidate file contains at most one outer tactic block.
One initially staged nested tactic opener in the threshold candidate was corrected
immediately; the current file has a single outer block and separate tactic branches.

## Four existing obligations

| Existing obligation | Preparation / dependency |
| --- | --- |
| `Params.seedBitsAt_le` | Exact all-Nat argument and a concrete sufficient C are in `payload-bound.md`. The construction-specific rounded-bucket product and tensor-length candidates in helpers/ supply its key steps. Requires proved positive widths and the existing `Encoding.W_le_ell_add_one` bound before using it. |
| `jls_seedBits_eq` | Complete short body candidate in `main/02-jls_seedBits_eq.proof`, using only already-proved owner field/seed-count readers and PolyExpr readers. |
| `jls_seedBits_le` | Complete short body candidate in `main/03-jls_seedBits_le.proof`; apply only after `seedBitsAt_le` and `jls_seedBits_eq` have actual proofs. |
| `jls_hasPolyStretch` | Explicit exponent choices and full eventual comparison argument in `stretch-gap-transfer.md`. Uses no security/locality assumption and no SubexpSmall fact. Exact E0 threshold and floor comparison candidates are staged. |

`helpers/01-E0_strict_gaps.proof` expects P, tau, h_tau:1<tau, and hE as in
jls_hasPolyStretch. Its goal is the pair
`5 < (P.E:Real)*(P.delta:Real)/2` and `5 < (P.E:Real)*(tau-1)`.
It uses E0_eq, Nat.lt_floor_add_one and positive-denominator order facts.

`helpers/02-B_mul_w_le.proof` expects P and kappa, with goal
`P.B kappa * P.w kappa <= kappa*(P.m kappa / P.w kappa+1)+P.w kappa`.
It is construction-specific rounding glue, not a duplicate generic division lemma.
It requires the existing upstream Params.noiseWidth_pos and W_pos to be proved.
It uses Core Nat.div_le_div_right, sub_le, add_div_right, div_div_eq_div_mul,
div_mul_le_self, lt_mul_div_succ and mul_div_left. No Floor.Div import is needed.

`helpers/03-tensor_le_two_pow_n_add_one.proof` expects P and kappa, with goal
`(P.ell kappa+1)^P.D <= 2^P.D*(P.n kappa+1)`.
It directly reuses public add_pow_le, then enlarges 2^(D-1) to 2^D.
This handles kappa=0 without a special tensor case. The source sketches' tensor
case proof should not duplicate the generic binomial/power estimate.

`helpers/04-w_le_n_add_one.proof` expects P and kappa, with goal w(kappa)<=n(kappa)+1; it consumes the already-stated Encoding.W_le_ell_add_one and Params.D_pos only after those have actual proofs.

`helpers/05-Encoding-W_le_ell_add_one.proof` is an untested replacement body for that existing Encoding theorem: separate ell=0, bound the floor/max by ell^(delta/2), square it, and use delta<1. It uses only existing upper-floor and Pow.Real APIs, so it does not require importing Floor.Semifield into Encoding.

The two `floor/` candidates have exact signatures in floor-rpow-reuse.md. They use
only public Mathlib facts and already-proved owner equations; no current sorried
StructuredSeed fact is a premise. The width comparison starts at kappa>=1; the
analogous all-kappa upper comparison would be false at zero due to max-one rounding.

## Shared API scope

The exact output polynomial majorant is the already-public
`Complexity.PolyExpr.eval_le` (Randomized/PolyExpr.lean:159). Read mBound by its own
reader and eval_subst, or apply G.outLen_le at n(kappa) and normalize with eval_le.
Do not reprove polynomial-expression growth by structural induction.

The shared Foundations.Subexponential file was inspected. Its public absorption
and reindexing results control `2^(-n^c)` advantages and are mandatory for the later
security milestones. M2 is a comparison of ordinary real powers with polynomial
lengths, so those exponential lemmas are not the right theorem here; no local
subexponential notion or duplicate absorption calculus is introduced.

The current precise import graph already covers the selected power, log/rate,
factorial, natural cast/division and polynomial-expression APIs. The one missing
floor-comparison root was identified before M0 and added by the lead. See
import-audit.md and its machine-readable graph snapshots. No broad unused import
or Stirling/SpecificAsymptotics root is recommended.
