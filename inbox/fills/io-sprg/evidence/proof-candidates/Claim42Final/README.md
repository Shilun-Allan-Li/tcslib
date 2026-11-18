# Claim42 final probability/analytic packet — NOT RUN

Read-only source preparation. No Lean/lake/build/cache, source edit, git mutation,
new import or agent spawn. The source head and exact required-module closure are
recorded in source-binding.json/current-import-closure.txt. All candidate proof
bodies are UNTESTED. Tactic refine holes have subsequent intended closing steps;
only actual Lean checks can establish that no goals remain. No proof, exact?,
apply?, seal or kernel success is claimed.

## Status

A full final claim42 body is staged, with full textual candidates for every new
specialized dependency, including the formerly missing joint Cond1/Cond2/Cond3
bounds. The most syntax-sensitive blocks are candidate13.hunif/htransport and
candidate05's transport through sdCore_draw/Draw. These are isolated haves for
small root pretests, not hidden algorithmic or mathematical assumptions.

Host: the area-local namespace
  TCSlib.Cryptography.Obfuscation.StructuredSeed.Internal
(the same Internal as Claim42.Load), inserted after Params' existing probability
estimates/decomposition and before the existing claim42. Reopen Params for its
body07. Add final source docstrings/citations, including Proof sketch for long
proofs, before landing helpers. The proposed theorems have no new definitions,
algorithms, samplers, attributes, notations or instances. Each candidate contains
one outer tactic block; root should preserve the per-invocation rule when testing.

## Dependency/test order

| File | Role | New dependencies |
|---|---|---|
|01 bucket_count_upper|all-kappa B <= m*kappa+1|none|
|02 prefactor_eventually_le_two_pow|eventually ((kappa+1)*B+1) <= 2^kappa|01|
|03 cond1_single_le_quarter|fixed-index Markov <=1/4 once log2(n)>=4*cLoc|existing cond1_prob_le|
|04 cond1_repetitions_fixed_index|actual independent secret/noise tuples, fixed I|03|
|05 cond1_all_fixed_index|full sdSampFull at fixed I, discard Boolean seed|04|
|06 cond1_all_joint|average over ACTUAL idSamp' law|05|
|08 binomial_ratio_quarter|choose(N,r)/B^r <=4^-kappa from base and r>=kappa|existing binomial_bound|
|09 bucket_count_lower|all-kappa m*kappa <= B*W|none|
|10 smallset_bucket_tail_quarter|fixed S.card<=Gamma<=B sparse bucket tail|08|
|11 capacity_bucket_tail_quarter|full-load capacity tail, kappa>=12|08,09|
|12 cond3_joint_le_quarter_pow|joint common capacity event, discard unused draws|11|
|13 cond2_sparse_joint_le_quarter_pow|joint sparse overload event, buckets sampled last|10|
|07 claim42.proof|EXISTING final body, common cutoff and event decomposition|02,06,12,13|

No source changes are requested for any upstream theorem statement. Existing
Claim42.Load fixed-placement bounds and Params' positive/eventual side conditions
remain upstream proof obligations, as root already assigned to other proof work.

## Exact estimates and common cutoff

For kappa>=12, Gamma<=B and log2(n)>=4*cLoc, uniformly for EVERY pp:
  Pr[Cond3] <= B*4^-kappa;
  for each k:Fin kappa, Pr[Cond2(k) AND NOT Cond1(k)] <= B*4^-kappa;
  Pr[forall k, Cond1(k)] <=4^-kappa.
Thus errProb <= ((kappa+1)*B+1)*4^-kappa.

The prefactor bound uses the explicit PolyExpr
  q(k)=(k+1)*(outBound(k^(E*D))*k+1)+1.
B<=m*k+1 and G.outLen_le imply the natural prefactor<=q.eval k for ALL k.
PolyExpr.eval_le supplies C,c with q.eval k<=C*(k+1)^c. The EXISTING limit
  tendsto_pow_const_div_const_pow_of_one_lt c (r=2) one_lt_two
is composed with Filter.tendsto_add_atTop_nat 1 and scaled by 2*C. Hence
2*C*(k+1)^c/2^(k+1) tends to zero and eventually is <=1. Ordered-field
algebra gives C*(k+1)^c<=2^k. This handles C=0 and c=0 without extra cases.
There is no custom subexponential definition or imported heavy bridge.

Final cutoff is max12(max kappaGamma(max kappaLog kappaPoly)).
All witnesses depend ONLY on P,cLoc and its stored output-bound expression.
Every pp is introduced AFTER that cutoff is chosen, preserving the required
uniformity. The final power equality is 2^k*(1/4)^k=(1/2)^k.

## Cond1: correct conditioning, actual tuple/product proof

Candidate03 does not divide by m, cLoc, Gamma or log(n). With W>0,
Nat.lt_mul_div_succ gives m*log(n)<W*(Gamma+1). Multiplying the existing
log lower bound by m yields 4*cLoc*m<=W*(Gamma+1), so cond1_prob_le<=1/4.
This includes m=0 and cLoc=0.

Candidate04 FIXES the entire index I (and hence G index). A repetition is
Secret x Noise. prodComm/uprob_fst discards the secret and matches exactly
the noise vector sampled by cond1_prob_le. OneWay.uprob_pi_forall then gives
q^kappa for the independent repetitions. Ordered power monotonicity bounds
this by4^-kappa. The theorem is valid at kappa=0 as a finite-tuple statement;
its hlog premise can naturally be false there.

Candidate05 transports the exact sdSampFull pushforward using expect_map,
prob_sample_eq_uprob and the published sdCore_draw reader, then discards the
Boolean seed with prodComm/uprob_fst. Candidate06 averages this UNIFORM bound
over idSamp' using prob_bind, expect_mono and expect_const. It never asserts
that Cond1 is independent after averaging over a shared G index, and never
assumes the G index law is uniform. Conditioning on full I is legitimate and
strong enough; extra fixed matrix/bucket coordinates do not affect the bound.

## Cond2: bucket map must be last

Candidate13 keeps the exact original G.IdDraw law, matrix, and full Draw.
Its first equality hunif rewrites jointLaw to the uniform product IdDraw x Draw
using published samplers/core readers, expectation map/bind/pure laws and the
existing expect_sample_pair/prob_sample_eq_uprob bridge. All statements are
PROBABILITY or EXPECTATION equalities, not free-OracleComp syntax equalities.

A composition of the public prodAssoc/prodCongr/prodComm equivalences changes
  ((GDraw x (Buck x Mat)) x Draw)
to
  ((GDraw x (Mat x Draw)) x Buck).
No bespoke choice equivalence or enumerator is introduced. The public badSet_eq
reader proves BAD independent of bucket labels. A local canonical zero bucket
function uses Fin0 with the existing B_pos proof; it is only a proof-facing
reference for S, never an honest encoder/preprocessor/default algorithm.

After fixing z=(G draw,matrix,Draw), S=BAD(z) is fixed before uniform Buck.
If card(S)<=Gamma, discard that conjunct and apply the fixed-set tail with
card(S)<=Gamma<=B. Otherwise the conjunction is impossible and has probability0.
Average the same bound with uexp_mono/uexp_const. In particular no assumption of
independence between different BAD output coordinates is made.

The exact syntax-sensitive transport target htransport is written in full in
candidate13. If opaque-type reader checks prevent its current change tactic,
repair only the type transport with idDraw_eq/draw_eq and the published core
readers; do not change any law, use off-support uniform G.Idx, or assert game
syntax equality. The remaining section argument is already isolated below it.

## Cond3 and numeric estimates

Candidate12 removes SdSamp via expect_map/expect_const. Its index event ignores
the generator draw and matrix; prodComm/uprob_fst retain the uniform Buck
marginal. The fixed full-load tail then applies. No actual index distribution
is replaced by an artificial uniform one.

Candidate08 uses the EXISTING binomial_bound once. With
  4*exp(1)*N <= B*r, r>=kappa, B,r>0,
its binomial ratio is <=(1/4)^r <=(1/4)^kappa by existing ordered-power APIs.
Candidates10/11 obtain 4*exp(1)<=12 from Real.exp_one_lt_d9.
For sparse S, card(S)<=B and12<=kappa imply the required base inequality at
r=kappa+1. For capacity, exact rounding gives m*kappa<=B*W; cap=kappa^2*W,
so cap>=W and cap>=kappa once kappa>=1. The chain
  4*exp(1)*m <=12*m <=kappa*m <=B*W <=B*(cap+1)
provides the base at r=cap+1. No cancellation by m and no log/floor/rational
noise-width asymptotic estimate is used. Strict thresholds always use t+1.

## Searches, overlap, and imports

Public name/shape searches covered Claim42/Cond1/Cond2/Cond3, badSet probability,
independent tuple events, PolyExpr evaluation/exponential domination, ceil bucket
quotients and binomial ratio/power bounds. No public exact construction-specific
helper statements were found; generic public APIs listed in APIs.tsv are reused.
In particular no Stirling, Markov, union bound, product-independence or generic
polynomial-growth proof is rederived. The short construction-specific quotient
bounds delegate division to Core Nat.lt_mul_div_succ and
Nat.div_le_iff_le_mul_add_pred. PolyExpr.eval_le handles generic polynomial growth.

No exact?/apply? scratch probe ran: those remain explicitly pending root before
landing new helper proofs. The static closure confirms every referenced module
already imported, including OneWayFunctions.Basic, Games.Bridges.Experiments,
SpecificLimits.Normed, Filter.AtTopBot.Basic, Topology.Order.OrderClosed,
Topology.Algebra.Monoid, Complex.ExponentialBounds, Nat.Log and all used tactics.
No new precise import is needed; no machine/sampler/efficiency work is added.
