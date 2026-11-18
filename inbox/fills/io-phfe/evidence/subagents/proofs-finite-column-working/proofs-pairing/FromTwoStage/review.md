# FromTwoStage exact-law bridge: skeleton and required probes

The frozen expectation theorem's complete docstring and header are unchanged in
expect_simGame_eq_saGame.skeleton.lean.inc. This is explicitly an incomplete
skeleton, not a completed proof: after splitting real/ideal and reading the exact
games it leaves both endpoint obligations admitted. The only tactic block in
this invocation is this existing theorem's skeleton. No new helper proof, Lean,
lake, Git, live-source edit or native checker was run. The proposed headers also
remain unverified until root runs the isolated typing/reuse probes.

## Three proposed logical helpers, probe before proving

RunProbeHeaders.lean imports the existing source module and gives three isolated
statements under namespace TwoStage, each with a term admission solely as a probe
placeholder. For each header root should first check its type, then run exact?
and apply? separately on the same goal. No new helper body should be drafted
before those results. A full-name and conclusion-shape source search found no
existing matching theorem; details are in searches.txt.

1. coinBlocks_ofFn_append is an implementation-layout reading, not a new coin
sampler or equivalence. It recovers both machines' typed tapes from their original
List.ofFn words concatenated in order. Its existing ingredients are firstCoins_eq,
secondCoins_eq, List.getD_append, List.getD_append_right, List.length_ofFn,
List.getD_eq_getElem, List.getElem_ofFn and Nat.add_sub_cancel_left.

2. simulate_toSA_real is an exact OracleComp equality for fixed arbitrary r,
pp, pk and msk. The right side is honest enc followed by the same q ordered
key calls and final second-machine activation. It has no randomness advance,
probability hypothesis, sampler or machine construction.

3. simulate_toSA_ideal is the analogous equality with one simulator state
threaded through enc and every key. Its StateT.mapM family deliberately retains
the full dependence of each key draw on its preceding simulator state. It does
not replace draws by a fixed Cartesian tape, assume key independence or discard
state before completing the ordered traversal.

Both protocol laws use exactly q+1 total calls via the existing toSA_run. They
also cover q.eval kappa = 0: the challenge consumes the only allowed query,
and the budget-zero buildComp still reads the final return. The first accepted
challenge always succeeds, and subsequent key calls always occur after it, so
no refusal branch affects these particular scripted runs. Arbitrary malformed
first-machine outputs remain covered because saCommitment and Commitment.decode
are the same total parser; no canonicality hypothesis is imposed.

## Existing API for the run-law proofs

Use toSA_run, saNext_nil/cons, saChallengeMove_eq, saKeyMove_eq and all four
buildComp case readers. The history induction invariant should retain the first
successful challenge entry and the prefix of already answered committed keys,
with remaining budget q minus the number of answered keys. The typed handler
readers real/idealSAImpl_eq, saImpl_zero/one_onSpec, real/idealSAChallenge_none
and real/idealSAKey_some give exactly the desired branch computations.

Read the challenge query using saSplitChallenge_fst/snd,
saChallengeQuery_eq and Fin.append_left/right. Read successful answer payloads
using saCTAnswer_eq/saSKAnswer_eq, Option.map_some,
FixedLengthScheme.decAnswer_some, Fin.cons_zero, Fin.tail_cons and the existing
saCTPayload_zero/saSKPayload_one equations. Thus filterMap over accepted keys
becomes the ordered list of encSK values by List.filterMap_map and
List.filterMap_eq_map'. viewWord_eq_viewWordBits then identifies the final word.

Use List.mapM_nil/cons/append/map (Lean 4.25 Init/Data/List/Monadic.lean), not
its tail-recursive mapM implementation or a newly written traversal.
For the ideal case only, StateT is the core function transformer; applying its
pure/bind actions to a state has the standard definitional equations in
Init/Control/State.lean. No published StateT.run_bind/pure theorem was found in
the repository's actual v4.25 toolchain; do not claim those names exist. Core
reduction is permitted by Rule 10; no TCSlib definition needs to be unfolded.
OracleComp.map_eq_bind, pure_bind, query_bind, bind_assoc and simulate_pure/query
supply the already published host laws; no host simulation lemma is re-proved.

## Completing the frozen endpoint after the run laws

The remaining expectation algebra needs no new sampling helper. Build the local
coin equivalence from the product of the two existing NUPPT.coinsEquivPoly rfl
maps, Fin.appendEquiv, and arrowCongr(finCongr lengthEquality)(Equiv.refl Bool).
The length equality follows from toSA_coins and PolyExpr.eval_add. Each shared
coin equivalence preserves List.ofFn via coinsEquivPoly_ofFn; Fin.appendEquiv_apply,
List.ofFn_fin_append and List.ofFn_congr therefore identify the joined tape word
with List.ofFn r1 ++ List.ofFn r2. Use coinBlocks_ofFn_append to read the two
blocks. This is a composition of public equivalences, not a custom sampler.

ProbComp.expect_sample_equiv reindexes the joined tape; the existing
ProbComp.expect_sample_pair in Games/Bridges/Experiments.lean:80 combines/splits
independent product samples (a precise additional import may be needed).
ProbComp.expect_expect_sample in Games/Probability.lean:326 commutes a uniform
coin sample across an arbitrary fixed ProbComp, so it handles pubGen/setup as
well as the stateful view law. expect_sample_comm alone only handles two sample
nodes and must not be claimed to commute an arbitrary algorithm computation.

Commute the first-stage sample before pp/setup because its commitment is a
function of r1 only. Move the independent second tape between its final position
and its position with r1 using expect_expect_sample; there is no private state
dependency in its sampling type. Read simGame_eq/saGame_eq, realView_eq/idealView_eq,
toSim_setup/enc/key, Commitment.omega_eq and viewWord_eq_viewWordBits, then apply
the appropriate fixed-tape protocol law. No exact syntax-tree equality between
the full games is claimed: only expectation equality after sample reordering.

## Modularity and size

The live FromTwoStage file has 280 lines. The three proposed headers total
about 40 lines; estimated combined proofs are 250-400 lines, plus 80-130 for the
endpoint sampling algebra. That projects roughly 650-850 lines and stays below
1000 without moving frozen declarations or introducing an import cycle. Start by
proving the coin reader, then the real fixed-tape law and the stateful ideal law
in separate invocations, each after root's native reuse probes. If either history
proof grows beyond 200 lines, report the exact invariant/helper statement before
adding a generic proof; do not insert a new higher-level algorithm bundle.

No mathematical counterexample was found. The obstruction here is proof size
and dependent history bookkeeping, not a false endpoint statement. The fixed-tape
helpers explicitly prevent a shortcut that would assume independent ideal key
draws or equate games with differently ordered independent samples.
