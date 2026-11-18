# Params bounds and inverse-power proof preparation

Fourteen unelaborated replacement bodies cover every existing nonreader Params.lean
stub. They add no definition, helper, assumption, or statement change. No Lean,
Lake, cache command, build, exact?/apply?, source mutation, or git mutation was run.
This packet is proof planning, not validation. All writes are under /private/tmp.

Snapshot HEAD: `55cb1147ff84f750a6b94f48103f6cc72d4fa036`. Params.lean SHA256:
`82f67d2f75d4e691e361a8e3bd273f59d02ad50ff53f0d697f592c9fc9843309`. Root has added the precise public padding import and moved the unchanged
le_n declaration earlier; the candidates use that current declaration order.

| Existing theorem and current line | Body | Inputs that must be proved first |
| --- | --- | --- |
| D_pos :276 | basic/01-D_pos.proof | one_le_d and D_eq; public natural division positivity. |
| noiseWidth_pos :281 | basic/02-noiseWidth_pos.proof | noiseWidth_eq and max lower bound. |
| noiseDenAt_pos :286 | basic/03-noiseDenAt_pos.proof | noiseWidth_pos and noiseDenAt_eq. |
| W_pos :291 | basic/04-W_pos.proof | noiseDenAt_pos and W_eq_noiseDenAt. |
| B_pos :296 | basic/05-B_pos.proof | B_eq and max lower bound. |
| kappaOf_pow :305 | inverse/01-kappaOf_pow.proof | one_le_E; public PadQuad.nu bounds and power order. |
| kappaOf_le :310 | inverse/02-kappaOf_le.proof | public PadQuad.nu_le. |
| kappaOfN_n :315 | inverse/03-kappaOfN_n.proof | D_pos, one_le_E; public PadQuad.nu bounds. |
| kappaOfN_le :320 | inverse/04-kappaOfN_le.proof | public PadQuad.nu_le. |
| lpnModulus_le_pow :326 | basic/08-lpnModulus_le_pow.proof | kappaOf_le and PrimeParam.le_two_pow. |
| lpnSamples_le :332 | basic/07-lpnSamples_le.proof | public PolyExpr.eval_pow/eval_var. |
| le_n :373 | basic/06-le_n.proof | D_pos, one_le_E; public Nat.le_pow. |
| Γ_le_B :379 | eventual/02-Gamma_le_B.proof | W_pos; existing generic logarithmic little-o API. |
| le_log_n :385 | eventual/01-le_log_n.proof | le_n; public Nat.le_log_of_pow_le. |

A green elaboration while any listed prerequisite still has a sorry would not
validate the conclusion. Root must discharge those prerequisites and inspect the
final dependency/axiom graph. No self theorem, downstream consequence, or current
sorried body was used as search evidence.

## Reuse and exact API locations

The shared search is exactly TCSlib.Cryptography.PadQuad.nu in
TCSlib/Cryptography/Asymptotic/UniversalPadding/Parameter.lean:
nu_eq :40, nu_pow_le :43, nu_le :48, le_nu :61. It already uses the bounded
Nat.findGreatest host. The four inverse candidates rewrite only published readers
into that API, then use power monotonicity for the exact-power equalities. There
is no duplicate proof of the generic bounded-search specification/maximality.

Core facts in the pinned Lean 4.25.0 source Init/Data/Nat/Lemmas.lean:
one_le_iff_ne_zero :145, div_pos_iff :888, div_le_div_right :928,
le_pow :1239, pow_le_pow_iff_left :1247. Nat.pow_le_pow_right is in
Init/Data/Nat/Basic.lean :782. Positive exponents imply E*D>=1; thus equal
positive powers recover the original base, including base zero.

PolyExpr.eval_var :118 and eval_pow :127 in
TCSlib/Complexity/Randomized/PolyExpr.lean settle the syntactic sample bound.
The stronger generic eval_le/eval_mono APIs were inspected but are unnecessary.
The modulus bound composes the public prime-width field with kappaOf_le and
natural exponent monotonicity. It never computes a prime.

Mathlib/Data/Nat/Log.lean :112, Nat.le_log_of_pow_le, gives le_log_n at the
concrete threshold 2^c using le_n. Root's declaration reorder makes this reuse
legal without reproducing the published own-domain lower bound inline.

Mathlib/Analysis/SpecialFunctions/Log/Base.lean provides logb_pow :120,
natLog_le_logb :417, and isLittleO_logb_id_atTop :513. The selected Γ proof uses
Asymptotics.IsLittleO.const_mul_left :1180, comp_tendsto :401, and eventuallyLE
:182 in Mathlib/Analysis/Asymptotics/Defs.lean. The natural cast tends to infinity
by tendsto_natCast_atTop_atTop in
Mathlib/Order/Filter/AtTopBot/Archimedean.lean :35.

Multiplying log_2 κ by the fixed real constant D*E is still little-o of κ.
Norm comparison gives eventually Nat.log 2 (n κ)<=κ, after reading n and ell
and using logb_pow. Multiplication and natural division are monotone; W>=1
ensures m*κ <= m*κ+W-1. Hence
floor(m*log_2(n)/W) <= floor((m*κ+W-1)/W) <= B.
No bound on G.outLen, noise asymptotic, rational-δ computation, or floor/rpow
approximation is needed for Γ_le_B. Positivity of noiseWidth also uses only its
max-one reader, not a floor lower bound. The earlier Stretch packet remains the
owner of the analytic floor/rpow approximation candidates.

## Imports and fidelity assessment

import-closure.json follows actual imports after removing nested Lean comments and
strings. Every selected public source is in the current Params transitive closure.
It is not a direct Mathlib cache-root ledger. Root reports 127 TCSlib modules and
83 direct Mathlib cache roots after adding UniversalPadding.Parameter, including
Algebra.Order.Ring.Nat as a new direct root although its olean was already available
transitively. The narrowed cache refresh belongs to root; none was attempted here.
No additional import request remains for this packet.

No actual false statement was found in this mathematical review. D>=1 and E>=1
handle inverse powers and le_n at κ=0. W and B remain positive at zero via max 1.
The logarithmic claims are eventual, so there is no demand that log(n κ)<=κ
hold at every small κ for arbitrarily large fixed E*D. The proofs preserve every
existing binder and the rational δ scope. No statement is weakened or extended.

The most likely mechanical risks are implicit arguments to PadQuad.nu equations,
normalizing both copies of the exact power under findGreatest, natural-to-real
cast rewriting under logb, and conversion from eventual norm bounds to Nat order.
The inverse candidates use simp only on published readers to normalize both
copies. The sole Γ proof has one outer tactic block, with bullet subgoals and no
nested tactic block. These risks await root's proof checks; no success is claimed.

## Recorded checks

reuse-searches.json records nine successful source-text searches with exact
commands and output. import-closure.json is a source import audit. static-checks.json
counts proof files, lines, widths, tactic-block tokens, and hashes; those checks do
not parse or elaborate Lean. SHA256SUMS binds this packet. There are fourteen body
files, each with at most one tactic block, no sorry/admit/axiom placeholders, and
no command that could invoke Lean. No helper source file was generated.
