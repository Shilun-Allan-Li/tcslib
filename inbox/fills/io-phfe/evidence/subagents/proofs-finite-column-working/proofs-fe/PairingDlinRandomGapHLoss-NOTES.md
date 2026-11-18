# Concrete DLIN random-gap ladder: isolated hLoss

Status: scratch proof-only fragment, inspection only; native verification/timing pending.
No Lean/lake/build/Git/live edits, process operation or extra agent was run. Exactly one
tactic block, four-space body, no holes/sorry, ≤100 columns. Local target unchanged:

  E_(publicParamsGen G kappa) loss = G.dlinMatrixSlack kappa.

This fills ONLY hLoss in the four-obligation ladder. hPoint and the two acceptance identities
are untouched. The source-clean freeze audit/pause is respected; only tmp artifacts are written.

## Explicit staged readers

Read dlinMatrixSlack_eq/publicParamsGen_eq and total expectation once, then compare the two
functions under the SAME original generator-coin sample with congrArg/funext. Fix rho.
Name exactly the reachable description constructed by the public-generation reader, without
choosing/recovering any other coins. expect_map reads the nonidentity-generator mapping and
inst_eq reads the RHS generated instance. No description injectivity is assumed.

hOrder is a concrete public core reader: PublicParams.group_eq followed by publicParamsCore_eq
identifies the actual core output's group order with group G kappa d.val. Its local proof uses
the required swap before the bullet. Scalar congruence then identifies the entire integrand
with the explicit constant c. The ONLY expect_const call has BOTH its sampled computation
and constant fully specified, and is applied once after hIntegrand.

No broad simp is used. No H/P/Q, D computation, game/sample acceptance law, prob_eq_expect or
arbitrary constancy matching appears. The dsimp-free change steps only name existing local
let d/c and local loss plus record/let reduction after published readers. All foreign group /
core / generation / instance functions are read explicitly through their public equations.

## Dependencies / semantics

Dependencies are existing proved readers: publicParamsGen_eq, publicParamsCore_eq,
PublicParams.group_eq, G.inst_eq, dlinMatrixSlack_eq and expect_bind/map/const. No diagonal,
rank, codec, game-equivalence, correctness or other pending admission is used. Generator
coin multiplicities and the independent nonidentity generator draw remain exactly the raw
public-parameter law. No sampler, machine, fixed modulus schedule, group representation,
scalar witness, DLOG or inverse encoder is introduced.

## Actual static reads/searches this invocation

Re-read Parameters.lean:130-156 for exact core/generation readers, Group.lean:313-322 for
inst_eq, and Probability.lean:127-140 / :171-177 for expect_bind/map/const. Read exact ladder
local loss and hLoss target. A narrow search for these reader combinations in Pairing/FE
found no additional needed API. The exact PublicParams.group_eq signature was inspected in
adjacent prior source reads and is used directly; no generated defining equation is named.

Native focus: matching the fixed local description d to the reader's let-bound description,
then the term-only scalar congruence from hOrder to loss/c. These are bounded metadata
normalizations independent of the previously suspected computational-test simp hotspot.
No performance/pass assertion is made before root's isolated native check.

All generation/slack/instance/core/group-reader rewrites in the saved fragment now supply
their concrete G/kappa/rho/d/g arguments explicitly. In particular the reflexive abbreviation
reader group_eq is pre-instantiated at the exact core output, avoiding reverse inference of
a PublicParams record from only its group-description projection.
