# Complete expectation-bridge proof candidate

The full frozen M0 docstring and declaration header are preserved unchanged.
The candidate has one tactic block, no admissions and no new public helper.
It is an unvalidated full candidate: no Lean, lake, Git, live edit or checker was
run by this agent. Both fixed-tape endpoint run laws, the generic stateful loop,
the lift traversal and the coin-block reader are now native PASS per root.
The new expectation body itself still requires native validation and its own
stored-declaration/axiom check.

Root is adding the precise import
TCSlib.Cryptography.Games.Bridges.Experiments.
Its exact product law is Games.Bridge.expect_sample_pair, NOT
ProbComp.expect_sample_pair as some earlier planning notes incorrectly called
it. This namespace/import correction was sent to root immediately when found.

## Proof decomposition and no syntax-tree assertion

The proof constructs only a local equivalence and pure real-valued functions
used inside the existing expectations. It creates no runtime sampler, machine,
implementation, adversary, draw type or algorithmic interface. Existing
ProbComp.sample occurrences instantiate the published reindex/Fubini facts.
No full-experiment OracleComp syntax equality is asserted.

hlen follows from NUPPT.coinLen_eq, TwoStage.toSA_coins and PolyExpr.eval_add.
The equivalence e is exactly Fin.appendEquiv followed by the existing
arrowCongr(finCongr hlen)(Equiv.refl Bool). Its domain is the original product of
machine Coins types, its codomain the existing joined adversary tape type.
No custom typeclass instances or chosen finite enumerations are introduced.
The hword proof reads this Mathlib equivalence as Fin.append precomposed with
the canonical Fin.cast, then uses List.ofFn_congr and List.ofFn_fin_append.
Only local aliases and Mathlib/core definitions reduce in change; no TCSlib
construction/coinLen body is unfolded.

The local result function is a pure expectation of the existing fixed-tape
experiment, not a new computation definition. hsa reads saGame_eq and moves the
independent joined tape before setup and then before public-parameter generation
using expect_expect_sample twice. It works in either real/ideal branch and does
not require setup/public parameters to be a single sample node.

hsplit uses expect_sample_equiv and Bridge.expect_sample_pair to reindex that
joined tape into independently uniform original first/second tapes. No uniform
finite-product or sampler-invariance fact is re-proved.

hfixed applies the already proved fixed-tape real/ideal run law. The published
coinBlocks_ofFn_append recovers r1/r2 from hword. saCommitment_eq therefore gives
the identical original first-stage commitment, and the second activation uses
the identical original second tape. realView_eq/idealView_eq, toSim_setup/enc/key
and Commitment.omega_eq identify the exact state-threaded views. No key-draw
independence or private-input disclosure to the simulator is assumed.

Finally simGame_eq exposes first-stage sampling before the view and second-stage
sampling after it. Pointwise in r1, expect_expect_sample commutes that independent
second tape across the entire real/ideal view computation. This closes the exact
expectation equality. The only reordered randomness is independent adversary
coins whose finite type does not depend on the view; stateful algorithm draws
retain their original order and dependencies.

## Native-check points and fallback guidance

- The precise Bridges.Experiments import must be present for the verified
  Bridge.expect_sample_pair name; its dependencies do not import FE and create
  no cycle. Root has already authorized/started that import addition.
- hsa intentionally uses only saGame_eq, expect_bind and two existing Fubini
  rewrites. If rewrite occurrence selection or the local result abbreviation
  hides the final reflexivity, make the same fixed-tape expectation explicit
  by change; do not unfold saGame, sample, expect or setup definitions.
- hword's change reduces the LOCAL e and Mathlib finCongr/arrowCongr, permitted
  by the boundary. Existing Games/Efficiency/Strings:573-577 uses the same
  appendEquiv/arrowCongr/ofFn_congr construction and is the fallback pattern.
- hfixed's simp is deliberately ordered with the exact joined-word equation,
  the run law, the commitment reader consequence and second-block reader. If
  simplifier child order leaves an original joined-tape occurrence, rewrite
  hword explicitly first, then apply the same published laws. Do not add a
  tape validity restriction or change any original machine output word.
- In the ideal branch, toSim state-family types may need an explicit local
  change/eta step around the mapM callback; the exact toSim/setup/enc/key and
  Commitment.omega readers provide the required law. There is no unproved
  equivalence of independent/state-dependent key draws hidden here.
- Each local placeholder proof uses the established swap/bullet convention;
  all remain in this one existing theorem's tactic block.

No mathematical obstruction found. Zero coin/key/bit dimensions use the
existing finite-function and Nonempty instances. No positivity, rank,
canonical-wire or efficiency hypothesis is added. The body has about 100 lines,
so the current module plus this endpoint remains below the 1000-line cap.
