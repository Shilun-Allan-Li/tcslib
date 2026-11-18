# M2 final stretch proof candidates — NOT RUN

Recommended bodies:
  01-seedBitsAt_le.proof
  07-jls_hasPolyStretch_direct_coefficient.proof
The second includes BOTH SP-W3 conjuncts. Supporting helpers are03,04,05.
Candidate02 and old body06 are SUPERSEDED, NOT APPROVED FOR LANDING; see below.
No Lean/lake/build/cache, source edit, git mutation, new import, sampler/machine,
efficiency proof or agent spawn. All strings are untested. No exact?/apply?,
compilation, tactic, kernel or seal success is claimed.

## Host and order

| File | Role | Upstream dependencies |
|---|---|---|
|01-seedBitsAt_le.proof|EXISTING Params.seedBitsAt_le body|Params D_pos/noiseWidth_pos/W_pos, Encoding.W_le_ell_add_one|
|03-w_lower.lean.candidate|new Internal pointwise rounded-width helper|owner readers, public Nat.div_two_lt_floor|
|04-stretch_gaps.lean.candidate|new Internal E0 strict-gap helper|E0_eq, Nat.lt_floor_add_one, D_pos|
|05-eventually_seed_relative_gap.lean.candidate|new Internal eventual seed<=m*kappa^-epsilon helper|01 and03|
|07-jls_hasPolyStretch_direct_coefficient.proof|EXISTING jls_hasPolyStretch body|04,05, PolyExpr.eval_le, jls_seedBits_eq, raw field readers|

Use namespace TCSlib.Cryptography.Obfuscation.StructuredSeed.Internal for03-05,
after the payload theorem and before the existing jls_hasPolyStretch. Add source
docstrings (Proof sketch for long proofs) and the exact helper overlap entries
before landing them. Every proof file has exactly ONE outer tactic block; normal
bullet subgoals remain inside it. No public definition or theorem header changes.

The existing jls_seedBits_eq bridge has an earlier candidate at
../Stretch/main/02-jls_seedBits_eq.proof. The all-parameter W_le_ell_add_one body
is at ../Stretch/helpers/05-Encoding-W_le_ell_add_one.proof; it handles ell=0
separately. Params positivity/basic candidates are in ../Params/basic/.
These are explicit existing proof dependencies, not added hypotheses or imported
sorried results claimed as established facts.

## Payload proof, including exact rounding and tensor steps

01 chooses C=2*2^D+12. For each kappa define
  K=kappa+1, X=n+m/w+1, a=2^D.
Existing add_pow_le and natural exponent monotonicity give
  (ell+1)^D<=a*(n+1)<=a*X,
including ell=0. Existing W_le_ell_add_one, w<=w^2 and ell<=ell^D give w<=X.

The rounded bucket product preserves its inverse-width saving:
  B<=m*kappa/W+1,
  B*w<=((m*kappa/w)/w)*w+w <=m*kappa/w+w
     <=kappa*(m/w+1)+w<=2*K*X.
Each step reuses named Core division inequalities (listed in APIs.tsv). No new
ceiling operator, quotient estimate, generic power bound or induction is added.

Since rc=kappa*w and t=kappa,
  B*(rc*t+t*rc)=2*kappa^2*(B*w)<=4*K^3*X.
Thus sLen<=(a+4)*K^3*X. The exact public/private count is
  kappa*n+1+kappa+2*kappa*sLen.
The first part is <=K*X, the second is bounded using the sLen estimate and
kappa<=K, and K<=K^4 gives total<=(2*a+12)*K^4*X. Multiplying by K proves the
existing fifth-power payload bound. There is no exceptional-parameter patch:
at kappa=0 the actual payload1 is covered by the same constant and X>=1.

## Analytic gap and final stretch route

04 reads E0's floor and proves
  g1=a*(tau-1)-5>0, g2=b-5>0,
where a=(E*D:Nat) cast Real and b=(E:Real)*(delta:Real)/2.
07 sets epsilon=min(g1,g2)/2>0. The exact inequalities supplied to05 are
  5+a+2*epsilon<=a*tau,
  5-b<=-2*epsilon.
No unnamed exponent gap or stronger schedule hypothesis is left.

At kappa>=1,03 gives kappa^b/2<=w via the existing multiplicative floor lemma.
Owner readers and rpow identities give n=kappa^a and kappa^(a*tau)<=m. The
public Nat.cast_div_le yields (m/w:Nat cast Real)<=m/wReal, and the positive
width comparison bounds that by2*m*kappa^-b. Also (kappa+1)^5<=32*kappa^5.
The three payload terms are bounded by
  kappa^5*n<=m*kappa^(-2*epsilon),
  kappa^5*m*kappa^-b<=m*kappa^(-2*epsilon),
  kappa^5<=m*kappa^(-2*epsilon).
Their weighted sum gives seedBitsAt<=128*C*m*kappa^(-2*epsilon).
The EXISTING tendsto_rpow_atTop, composed with tendsto_natCast_atTop_atTop,
provides eventually128*C<=kappa^epsilon.05 then collects powers to obtain
  seedBitsAt<=m*kappa^-epsilon.
No custom asymptotic/subexponential notion or generic floor asymptotic is added.

The preferred07 uses PolyExpr.eval_le DIRECTLY for
  q=outBound.subst(pow var (E*D)).
It retains the constant: m<=C0*(kappa+1)^c<=D*kappa^c for
  D=max1(C0*2^c).
It does NOT prove eventual m<=kappa^K. Set
  eta=epsilon/(2*(c+1)), tauPrime=1+eta>1.
A SECOND application of the same existing positive-power limit supplies
  D^eta<=kappa^(epsilon/2)
eventually. Thus
  m^eta<=D^eta*kappa^(c*eta),
  seedBits^tauPrime<=m*kappa^(epsilon/2+c*eta-epsilon*tauPrime)<=m,
because (c+1)*eta=epsilon/2, eta>0 and tauPrime>1. All exponent equalities,
positive bases and monotonicity steps are named haves in07.
See direct-coefficient-route.md for the precise comparison sequence.

## SP-W3 and uniformity

The repaired Raw.hasPolyStretch_iff is consumed exactly. The growth conjunct
uses the stronger all-kappa bound kappa+1<=seedBitsAt, since pubLen>=1 and the
residue width is kappa+1. It needs no added hypothesis or asymptotic step.
The power conjunct uses jls_seedBits_eq and jlsSPRG_raw_outLen. The common cutoff
is max1(max kappaSeedGap kappaCoefficient), chosen before the prime schedule is
read by any length equation. All analytic witnesses depend only on P,tau and
its stored polynomial bounds. No p/pp-specific threshold is selected.

## Reuse decision and rejected exploration

Public PadQuad.exists_pow_dominates in Asymptotic/UniversalPadding.lean:75 proves
generic PolyExpr eventual monic-power domination. Its owner is absent from the
current Stretch closure (Parameter alone is present); adding its owner would
load Collections plus BinaryRoot/Machine. No import is proposed.

ROOT REVIEW rejected duplicating that normal-form absorption merely with an
overlap disclosure. Accordingly02-output_power_bound and its dependent old06
are preserved as SUPERSEDED EXPLORATION, NOT approved candidates for landing.
Disclosure alone is not permission to duplicate an existing public theorem.
The adopted07 avoids the monic-normalization result altogether: it retains the
coefficient and absorbs its eta power directly with a public rpow-growth API.
No downstream approval or gap concerning that generic lemma is needed on07.

Other overlaps are consumed directly: add_pow_le, Core Nat division/power
inequalities, Nat.div_two_lt_floor, Nat.lt_floor_add_one, PolyExpr.eval_le and
the public Real.rpow/filter APIs. No generic normal-form proof, polynomial
induction, floor comparison or growth theorem is reproved. Searches covered
exact helper names and seed/stretch/rpow shapes; none of the three proposed
Internal construction-specific helper statements had a public equivalent in
the allowed current closure. Required exact?/apply? probes remain pending root.

## Verification boundary

The intended complete bodies contain no intentional missing mathematical goal,
but only Lean can verify closure of refine subgoals and coercion inference.
Most sensitive haves:01's natural polynomial normalization;05's cast division,
reverse rpow_mul and final exponent collection;07's eta denominator cancellation,
power-product rewrite and actual field-reader transfer. Test those isolated
haves if needed; do not silently change statements or drop SP-W3.

Static closure confirms Floor.Semifield, Pow.Asymptotics/Real,
Nat.Cast.Order.Field, Order.Ring.Basic, Filter.AtTopBot.Tendsto/Archimedean,
PolyExpr and required tactics are already reachable. No new import/header root
is needed. source-binding.json and static-checks.json report only text/static
facts, not elaboration or proof status.
