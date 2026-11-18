# Concrete DLIN random-gap ladder: isolated hPoint

Status: scratch proof-only fragment, inspection only; native verification/timing pending.
No Lean/lake/build/Git/live edits, process inspection/termination or extra agent was run.
Exactly one tactic block, four-space body, no holes/sorry, ≤100 columns. Main and local
frozen targets unchanged. This fills ONLY hPoint in the four-obligation ladder; hLoss and
both acceptance-normalization obligations are untouched.

Exact local context/target: pp is already the explicit parameter of
`hPoint (pp : PublicParams G κ) : |P pp-Q pp| ≤ loss pp`.
Do not intro pp again. H/P/Q/loss are exactly the definitions in
PairingDlinMatrixGameRandomGapLe.ladder.lean.inc.

## Reduced inference surface

The Field/ZMod prime and nonzero instances are given directly from pp.group.order_prime,
so no global BilinearGroup reverse-instance search is required. All ab/u/coin types are
explicit. The local obs predicate is the identical actual distinguisher test already in H;
its encoding is never simplified or evaluated. h0/h1 explicitly name BOTH the sample
computation and predicate, avoiding the original `prob_nonneg _ _` / `prob_le_one _ _`
metavariables under dependent callbacks.

The generic lemma explicitly gets K:=ZMod pp.group.order and H pp, with these named bounds.
Only local aliases P/Q/loss are reduced. The final simpa has exactly ONE public lemma,
ZMod.card, and does not expand H, either game/sample law, prob_eq_expect, or expect_const.
Thus this checkpoint isolates application/field-cardinality inference from the previously
suspected large probability-normalization step. No performance fix or pass is claimed until
root runs the checkpoint; the earlier hotspot ranking was static, not measured here.

## Dependencies / unchanged semantics

The generic dlinDiagonal_random_gap_le is parent-reported fully proved/native fast with
zero admissions. Existing prob_nonneg/prob_le_one and ZMod.card are the only other theorem
dependencies. The local obs merely names the same proof predicate; no new helper theorem,
public algorithm, sampler, machine, efficiency witness, group representation, scalar witness,
DLOG or inverse encoding is introduced. The duplicate literal test in obs is a local typing
annotation, not a new serialization layout; no foreign body is explicitly unfolded.

## Actual source reads/searches this invocation

Read the exact ladder's H/P/Q/loss and hPoint target; current Diagonal.lean:43-59 for the
proved helper signature. Re-read Probability.lean:228-243 for exact probability range
lemmas and Group.lean:163-172 for existing factPrime/neZeroOrder field contracts. Ran narrow
searches for explicit local Fact/NeZero/diagonal helper uses in Linear/Diagonal. No new API
is needed. No native search was re-run, and no admission status outside this checkpoint is
claimed changed.

Potential native check focus: definitional equality of the typed local obs probability
with H at fixed pp/ab/u, and standard proof-irrelevant agreement of the explicit local
prime/nonzero instances with the existing sampled ZMod types. No broad simp is present.
