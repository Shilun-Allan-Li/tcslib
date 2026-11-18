# BilinearGen.dlinMatrixGame_random_gap_le consumer candidate

Status: scratch full proof candidate checked by inspection only; native verification pending.
No Lean/lake/build/Git/live edit/extra agent was run. Frozen main header/prose copied byte-
for-byte; one tactic block, no remaining holes/sorry, no new helper/interface/algorithm,
all lines ≤100 columns. Parent reported the generic diagonal lemma now native rc0/both-error
counts0 with ZERO admissions; this consumer itself is not claimed checked or standard-only.

## Exact pointwise test and averaging

H pp ab u is the actual distinguisher's acceptance probability over its existing machine
coins, on the actual G.dlinEnc/G.dlinChallenge formed from pp, the two base exponents ab and
three response exponents u. It retains the base metadata ab and never recovers any scalar
from a group point. H is only a local proof test expression, not a sampler, machine builder,
new public algorithm or efficiency witness. prob_nonneg/prob_le_one supply its [0,1] bounds.

Local P/Q are precisely the uniform and diagonally multiplied response expectations in the
proved dlinDiagonal_random_gap_le. ZMod.card identifies the field cardinality with pp.group.
order. BilinearGroup.factPrime supplies the existing field instance; no fixed order schedule
is assumed. hPoint applies the exact diagonal theorem with loss 2/p-1/p² for each pp.

hLoss reads publicParamsGen_eq, expect_bind/map and publicParamsCore_eq. The loss depends
only on the description's group order, so the additional nonidentity-generator draw has a
constant expectation and disappears via expect_const. dlinMatrixSlack_eq and G.inst_eq
identify the remaining average over the ORIGINAL generator coins. Multiple coin strings
with one description are preserved correctly; no desc injectivity or dependent-sum sample
is assumed. hPoint and hLoss both include swap before their local proof bullets.

abs_expect_sub_le_expect averages hPoint over publicParamsGen G κ. The actual false-game
readers and probability/expectation readers normalize to exactly P/Q. The matrix experiment's
unused rs draw integrates out via expect_const. The canonical response vector literal is
read with Matrix.cons_val_zero/one/two and head_cons/tail_cons; no alternate encoding or
generated foreign equation is used. The final simpa identifies hAverage with the frozen goal.

## Slack scope / no double counting

This candidate proves ONLY the frozen comparison between compressed matrix DLIN and the
canonical DLIN random presentations. It does not edit or add slack to any direct MDDH bound,
quadratic-security reduction or headline. Their direct canonical reductions already account
for their own zero-coordinate failures. This dlinMatrixSlack is used once here, matching
its existing definition exactly.

## Actual source/API searches and inspections

Read current Pairing/Linear.lean:185-228, :248-296 and :303-340 for the two exact false
sampling laws, game readers, slack and frozen main target. Read Parameters.lean around
publicParamsCore_eq/publicParamsGen_eq (current :130-155) and Group.lean:313-323 for inst_eq.
Read Probability.lean:205-228 and :404-417 for probability readers and exact averaging API.

Searched prob_eq_expect/nonnegative/one-bound parallels and publicParamsGen_eq/inst_eq use
in Pairing/FE. Verified Group.lean:166-170 supplies factPrime/neZeroOrder. Re-read current
Diagonal import header and parent native status: the independent module imports Exponents,
Games.Probability, Games.Bridges.Experiments and OneWayFunctions.Basic; parent is adding its
import to Linear/facade. No new Mathlib root is requested by this consumer.

Searched finite-vector head/tail readers in Mathlib/Data/Fin/VecNotation.lean and inspected
head_cons (190), tail_cons (194), cons_val_zero (122), cons_val_one (234), cons_val_two (237).
Only published equations are passed to simp/rw. All explicit local unfolding is limited to
H/P/Q/loss proof aliases. PublicParams.group is the existing permitted reducible notation.

Reused exact theorem dependencies: proved dlinDiagonal_random_gap_le; existing
ProbComp.prob_nonneg/prob_le_one, abs_expect_sub_le_expect, expect_bind/map/pure/const,
prob_bind/pure/eq_expect, publicParamsGen_eq/publicParamsCore_eq, G.inst_eq,
dlinMatrixSlack_eq and existing DLIN sample/game/encoding constructor functions. The
encoding/injectivity/length/correctness admissions are not used. dlinMatrix_mulVec remains
unneeded because the frozen compressed sample reader already spells out the coordinates.

## Native integration focus

The substantive mathematics is provided by the now-proved diagonal theorem. Unchecked
elaboration details are dependent local-test inference, exact ZMod field-cardinality
normalization, recursive false-game probability simplification, and dependent record
projection normalization in hLoss. If a type/normalization issue occurs, isolate that exact
reader subgoal; no new generic helper or statement change is currently required.
