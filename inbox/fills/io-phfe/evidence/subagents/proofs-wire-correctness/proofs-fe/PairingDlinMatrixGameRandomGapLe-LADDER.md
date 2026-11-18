# Random-gap consumer: static hotspot review and smaller sorry ladder

Status: STATIC DIAGNOSIS / SCRATCH LADDER ONLY. No Lean/lake/build/Git/live edit, process
inspection/termination, or extra agent was run. Root owns termination of its recorded PID
and the native checkpoints. The current whole proof was CPU-bound per root; no precise
hotspot is experimentally identified here. The generic diagonal helper is already native
fast, fully proved, and is not the suspected mathematical bottleneck.

## Proposed one-block ladder

PairingDlinMatrixGameRandomGapLe.ladder.lean.inc preserves the original exact frozen header
and local H/P/Q/loss definitions. It contains exactly FOUR explicit local admissions:

1. hPoint: bounded test + generic diagonal lemma / ZMod.card.
2. hLoss: publicParamsGen/core/map/const + inst_eq slack identification.
3. hMatrixAccept: actual matrix false acceptance = E_public P.
4. hTupleAccept: actual canonical false acceptance = E_public Q.

The final assembly is now ONLY two equation rewrites and abs_expect_sub_le_expect. It runs
no broad simp, expands no test, and calls no new generic helper. The two acceptance identities
split the former large 'final assembly' normalization into independent directions, so native
checking can distinguish actual law-reader work from inequality assembly. All four holes
remain admitted until root fills/checks one at a time. No proof pass is claimed.

## Most likely hotspots, ranked but NOT confirmed

1. The original final `simpa only [P,Q,H,...] using hAverage` expands the dependent test and
   three nested sample/continuation layers on BOTH the goal and hAverage. It mixes two
   overlapping normalizations of prob: general prob_eq_expect and bind-specific prob_bind /
   prob_pure. This is not an apparent rewrite CYCLE (all those readers point to expectations),
   but it creates a large duplicate normalization and higher-order matching problem.
2. In that same broad simp, unconditional expect_const repeatedly attempts to recognize a
   constant integrand even after H has exposed the full distinguisher/encoding expression.
   A failed constancy match may invoke expensive definitional unification through these
   terms. This is the strongest static reason to KEEP H FOLDED during sample normalization
   and apply expect_const to ONE explicitly identified unused draw at a time.
3. hPoint has underconstrained `_ _` probability bound terms plus implicit Field/Fintype
   resolution for ZMod pp.group.order. Likely small, but root's isolated checkpoint can test
   this before blaming final simp. Explicit K/H argument and fully typed bound lambdas (or
   explicit local Fact prime / NeZero order instances) avoid broad class/unification search.
4. hLoss's all-in-one simp is much smaller and contains no D, but can also be staged if needed.

No static evidence suggests an incorrect inequality, a false distribution claim, or a need
to increase the mathematical slack. No statement/algorithm/sampler change is recommended.

## Recommended native checkpoint order

* First compile the all-four-sorry ladder with its tiny completed assembly. If it is still
  slow, the issue lies in local definition/typed target elaboration, not any proof tactic.
* Fill ONLY hPoint. Prefer explicit `(K := ZMod pp.group.order)` on the diagonal theorem,
  name typed hH0/hH1 before application, then rewrite its RHS with ZMod.card. Avoid any
  game/sample/H-body simplification in this checkpoint.
* Fill ONLY hLoss. Read slack/publicParamsGen and expect_bind first, fix one generator-coin
  rho binder, then expect_map and publicParamsCore_eq. Integrate the nonidentity-generator
  sample with expect_const whose computation AND constant are explicit. Finally inst_eq.
* Check hMatrixAccept separately, then hTupleAccept. Keep P/Q/H folded until a single leaf
  observer equality has been normalized. Each identity needs only its OWN game/sample reader.

The existing maximum-heartbeat-zero source setting means root may choose a bounded diagnostic
probe to locate the exact phase; this agent did not change options or execute any probe.

## Smaller acceptance-normalization strategy

Read accept_eq and the relevant game reader. Use prob_bind for the outer game and expect_bind
for that sample's own scalar draws, rather than also applying general prob_eq_expect at every
node. Reduce ONLY the closed false branches. Identify one unused draw explicitly:

* Matrix false: rs is unused; its remaining continuation is E_u of the actual observer.
* Canonical false: all three scalar draws are used, so no scalar expect_const step is needed.

At the leaf, the concrete goal is exactly the generic observer identity

  prob ((sample D.Coins).bind (fun r => pure(verdict r))) (·=true)
    = prob (sample D.Coins) (fun r => verdict r=true).

Its existing readers are prob_bind, prob_pure, then reverse prob_eq_expect. This can be
applied in ONE fixed leaf scope/word input while treating verdict or the encoded word as a
local opaque argument, so simp need not inspect D's machine computation. No new helper proof
is supplied here; root can use a local equality or request a shared probe if it wants that
identity as public API. A static search found no published prob_map/prob_bind_pure variant
in Games/Foundations. OracleComp.map_eq_bind exists, but expect_map would still need the same
leaf probability reader; no sampler or algorithm bridge should be introduced.

Only after those leafs match H should the function identities be reassembled by congrArg /
funext at public/scalar binders. Use explicit expect_const c r on the known unused draw,
not recursive simp's unrestricted expect_const rule over exposed machine terms.

## Actual static inspections / nearest API reuse

Read the entire candidate, Probability.prob_eq_expect/prob_bind/prob_pure and existing source
uses in Pairing/Assumptions and BonehBoyenSecurity. Existing successful proofs stage outer
probability readers before pointwise/case/expectation work. Read Parameters public generation
and Group factPrime/neZeroOrder instance shapes to identify possible typeclass matching.

Searched prob_map/prob_bind_pure/prob_bind_pure_comp/accept_map and equivalent patterns in
Games/Foundations/Mathlib Probability; none directly matches in the inspected scope. Located
OracleComp.map_eq_bind (111), pure_bind (115), bind_pure (124); no helper was re-proved.
Read native-independent existing BonehBoyenSecurity:118-139, which applies averaging then
works pointwise instead of unfolding the entire final comparison at once.

Additional reuse improvement for later skeletons (not an extra proof this invocation):
Mathlib's abs_sub_le_of_nonneg_of_le already combines the four [0,1] bounds and is used in
BonehBoyenSecurity:129-132. The small-row skeleton's arithmetic entry bound could consume
that directly after native inspection rather than repeat range linarith; no live change was
made and no new generic interval helper is needed.

The original full candidate and all prior evidence are retained unchanged. This diagnostic
ladder is a safer checkpoint layout, not evidence that the original mathematics is false or
that any of the newly isolated obligations has passed.
