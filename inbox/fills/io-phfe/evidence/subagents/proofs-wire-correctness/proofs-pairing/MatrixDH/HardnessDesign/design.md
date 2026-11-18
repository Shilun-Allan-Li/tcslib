# MDDH hardness modularity: three targets, no proofs

This is DESIGN/STATIC SEARCH ONLY: three helper headers/docstrings, anonymous exact?%
probes/order, relocation metadata and import checks. ZERO tactic blocks, no helper
proof, source edit, runtime definition, machine/realiser construction, Lean/lake/Git
command, cache operation, new Mathlib root, or frozen-header change. Native typing
and exact/apply gates are required before authorizing any helper proof.

## Lower module and dependency direction

New owned Pairing/MatrixDH/Hardness.lean imports MatrixDH.Defs, allowed
Foundations.Subexponential, and the explicitly authorized existing Asymptotic.EnsemblesLemmas
for the third negligible-consequence helper. Defs already supplies PolyExpr/NUPPT, matrix advantages,
DLIN assumptions, and the public advantage readers. Static closure has NO SelfReduction
or CoinSampling.Asymptotic and introduces no Mathlib module not already reachable from
current SelfReduction. Thus SelfReduction -> Hardness -> Defs is cycle-free.
Root can expose Hardness from the MatrixDH facade when integrating. No import changes
were made here. Probes import only those lower roots plus permitted core LibrarySearch;
they never import SelfReduction, Hardness stubs, or an admitted target.

## Target 1: MOVE the fixed correction proof, do not copy it

Name: BilinearGen.mddhCorrection_subexpSmall. Its explicit lambda is exactly
(d.eval kappa : Real)*(4/(p kappa : Real)); it mentions no mddhSlack runtime definition
or generator. Hypotheses are exactly exponential schedule growth and 0<c<1, with no
prime/positivity/efficiency/dimension restrictions added.

The existing proved mddhSlack_subexpSmall mathematics must be MOVED into this helper
AFTER its native gate. relocation.json records the current source/body hashes and line
span; the body is deliberately NOT copied into this artifact. The only body adaptation
is removing mddhSlack_eq from the final reader rewrite, since the goal already contains
the explicit lambda formula. All primitive decay/closure lemmas remain consumed whole.

The ORIGINAL frozen mddhSlack_subexpSmall header/prose stays in SelfReduction. Its short
body calls the new explicit theorem and transports through the pointwise mddhSlack_eq
reader, using function extensionality or SubexpSmall.mono with equality of absolute
values. Do not assume simp can rewrite an unapplied function using a pointwise reader.
Delete the old mathematical body there in the same integration change so only ONE copy
remains. No generic polynomial-times-exponential helper is introduced.

Nearest generic polynomial closure is CoinSampling.subexpSmall_polyExpr_mul, with its
polyExpr_eval_le_mul_pow majorant. That module is FORBIDDEN by dispatch; it is not
imported or copied. The relocated fixed-4d/p proof uses allowed PolyExpr.eval_le and
Foundations primitives exactly as its already-approved frozen proof.

## Target 2: assume the quantitative bound, prove common-exponent hardness

Name: BilinearGen.mddh_subexpHard_of_adv_le. beta is any fixed Nat->Real function.
The correction hypothesis holds at every exponent in (0,1). The bound quantifiers are
EXACTLY forall machine D, exists ONE machine B, forall kappa. They must not become
forall kappa exists B. No advice/RealizesOn/hR identifier occurs in this lower theorem.
It asserts no realiser construction; it is a logical closure consequence of the supplied
bound and SubexpDLIN. No positivity assumption on beta is needed.

Faithful proof plan (NOT a proof draft):
1. Read G.subexpDLIN_iff and subexpHard_iff to obtain a>0 and a bound for EVERY B.
2. Choose eta=min(a,1)/4 BEFORE D. Then eta>0, 3eta<a, 2eta<1.
3. Choose the fixed d majorant via PolyExpr.eval_le. For kappa>=1 its elementary bound
   d(kappa)<=C*2^k*kappa^k specializes to the weighted DLIN term.
4. For a D choose the B supplied by hBound. Apply the EXISTING .mul_pow from a to
   3eta and .const_mul from 3eta to 2eta. Apply .mono to get d*DLINadv at 2eta.
5. hbeta at 2eta supplies the other term. EXISTING .add gives exponent eta.
6. mddhAdv_eq plus advantage_nonneg and the pointwise bound, followed by le_abs_self,
   give .mono for the actual advantage. Use subexpHard_iff with eta outside forall D.
Thresholds may depend on B/D, as SubexpHard permits; the exponent may NOT.
The only additions are specialized MDDH scalar arithmetic and quantifier glue, not a
copy of a generic polynomial closure or a new decay/absorption proof.

The ORIGINAL frozen mddh_subexpHard becomes a short consumer: apply this helper at
beta=mddhSlack p d; use the preserved correction wrapper for hbeta; for each machine D,
obtain omega from mddhAdv_le, then its B from mddhRealizable_iff hR and return that
same B's all-kappa inequality. Pass hSubexpDLIN. This preserves the realisability
quantifier scope and adds no hypothesis over arbitrary typed adversaries.

## Target 3: move the negligible-consequence consumer logic lower

Name: BilinearGen.mddh_negligible_of_adv_le, explicitly authorized by root after the
source-size read grew to approximately 1000. beta is a fixed negligible function,
hBound again has forall D exists ONE B forall kappa, and h is G.DLINAssumption.
The conclusion is forall D, Negligible(G.mddhAdv d l D). No SubexpDLIN hypothesis is
substituted for ordinary DLIN hardness, and beta need not be separately nonnegative.

After the native gate, specialize the already-drafted consumer logic to hBound/hbeta:
for D obtain B; dlinAssumption_iff gives its negligible advantage; EXISTING
EnsembleLemmas.negligible_polyExpr_mul, Negligible.add and .mono finish. The same
mddhAdv_eq/advantage_nonneg/le_abs_self route handles absolute values. This is a
MDDH consequence, not another generic polynomial/negligibility theorem.

The ORIGINAL frozen mddhAdv_negligible becomes a short advice/realiser consumer of
this helper. Its hbeta comes from the preserved correction wrapper at exponent 1/2
and EXISTING SubexpSmall.negligible. Its hBound obtains omega/B exactly as the
subexponential wrapper. Move the drafted downstream consequence logic here rather
than keeping a second whole closure proof in SelfReduction.

The extra direct import is existing Asymptotic.EnsemblesLemmas, already imported by
SelfReduction and explicitly named by root for this consequence. Static closure stays
cycle-free and adds ZERO Mathlib module names relative to current SelfReduction.
No CoinSampling.Asymptotic import or generic closure copy is introduced.

## Size ledger and remaining risk

At the relocation read SelfReduction had ALREADY grown to 999 lines during root's
parallel hybrid integration (the initial task quoted 891). Its existing correction
mathematical body remains 49 lines. Replacing that body by a 3-4 line reader wrapper
saves 45-46 lines, with one new Hardness import. The frozen header/opening prose remain
unchanged. Headers for both original asymptotic consequences are already in that total.

With BOTH consequences factored, target their downstream bodies at 6-8 lines each
(instead of the previously estimated ~20/~50). That is approximately 5-7 added lines
per existing admitted body. From the 999-line snapshot, the projected count BEFORE
remaining hRead/type growth is about 999-46+7+7+1=968 on the conservative 8-line
consumer-body budget. A net 30-line remaining hRead fill then gives about 998.
Additional explicit-type repairs can still consume that small margin. This is a budget
plan, not a guarantee: root MUST recount after the move and actual hRead integration.
If it exceeds 1000, another independent lower proof or slimmer consumer term is needed;
this design does not pretend the hard cap has already been met.

Hardness itself should remain below roughly 300 lines after the moved ~49-line proof,
the specialized common-exponent closure, and the short negligible consequence.
There is no mathematical obstruction found in the THREE proposed targets. Native
typing/exact/apply gates must precede proof relocation or helper fills.
