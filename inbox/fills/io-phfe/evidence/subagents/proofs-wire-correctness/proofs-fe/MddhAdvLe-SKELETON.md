# Direct canonical DLIN-to-MDDH: original theorem sorry ladder

STATUS: SCRATCH SKELETON, NOT A COMPLETE PROOF. EXACTLY SIX named term sorries remain:
hEnds, hPreScalar, hRealClose, hRandomClose, hLossBudget, hCoinUnwrap. No main/security/
standard-only completion claim is made. All remaining structural tactics are candidate
code requiring root-native typing and Rule 10 checks. No Lean/lake/build/Git/live edit/
process operation/extra agent/native search was run by this child.

Candidate: MddhAdvLe.skeleton.lean.inc (191 lines). One tactic block, <=100 columns.
The exact frozen original mddhAdv_le statement prose/header was copied byte-for-byte
from CURRENT SelfReduction.lean. No interface statement change or added hypothesis.
Eleven local tactic/refine/calc goals have seven swap/bullet branches plus the direct
pair-refine/calc continuations; this is a proposed ladder, not a verified goal census.

## Actual experiments, advice and quantifier order

hybrid(kappa,i) is EXPLICIT actual probability code: sequential publicParamsGen, uniform
scalar M (ell x 2), S (2 x d), U (ell x d), then original D.Coins. Its response column b is
(M*S)_b if b.val<i and U_b otherwise. The base and response are exponentiated by the actual
public generator and encoded by G.mddhEnc; no abstract unbound hybrid scalar is introduced.
Thus hybrid0 is all-random and hybrid(d) all-real, including d=0.

redGame(kappa,w,real) is EXPLICIT actual canonical G.dlinSample followed by original D coins
and D.distinguisherL on the PUBLISHED G.mddhPre word. redGap is the existing Games.advantage
of those two semantic experiments. These are proof-local probability games, not new runtime
algorithms or sampler/machine implementations. The reduction remains the existing deterministic
dlinToMddh; hCoinUnwrap is the precise bridge between its length-limited list activation and
this typed semantic redGame.

Tape(kappa) is exactly the THREE existing scalar matrices (L,S,U), over p(kappa).
avgTape is only proof-local notation for the existing ProbComp.expect(sample Tape) with
orderSchedule_neZero installed. The hybrid INDEX IS FIXED before averaging; the proof does
NOT sample the entire MddhAdvice including its d+1 sentinel index, which would insert an
unwanted extra dimension factor. No product sampler is constructed; this is only an exact
finite uniform law on the already explicit product draw type.

hPointwise(kappa) selects one actual w, with no B or realisability input. At d=0 it uses the
PUBLISHED mddhAdviceDefault sentinel and proves zero advantage via coincident endpoints.
At d>0 it calls the PUBLISHED exists_advantage_hybrid_gap to pick j<d, then the PUBLISHED
LamportReduction.exists_expect_sample_le to select the scalar tape for THAT j. The returned
advice index is i.castSucc : Fin(d+1); it is never the sentinel in this branch.

Only AFTER hPointwise does Classical.choose assemble omega(kappa) and choose_spec its bound.
Only AFTER omega is fixed does the proof introduce arbitrary B and its RealizesOn evidence,
then kappa. Consequently ONE omega family works for EVERY realiser and EVERY parameter;
there is no B-dependent advice selection. This is the literal frozen quantifier order.

R-DLOG note: Classical.choose here selects finite scalar ADVICE from hPointwise; it NEVER
chooses an exponent witness of a group element. The only scalar group expressions in
hPreScalar arise from the KNOWN canonical sample draws ab/rs/t and known advice matrices.
No algorithm recovers a scalar from a group point, decodes a group logarithm, or samples.

## Exact six remaining obligations / intended reuse

1. hEnds: actual all-random/all-real hybrid endpoints equal actual mddhGame acceptance.
   Read mddhGame_eq/mddhSample_eq and the probability readers, use j<d for the last endpoint,
   and finite-matrix function extensionality. This also covers d=0. It is a real law bridge,
   not an endpoint assertion assumed in a changed theorem.
2. hPreScalar: EXPLICIT actual group-arithmetic identity for mddhPreChallenge on an actual
   canonical DLIN draw. It casts advice using the same ringEquivCongr as the definition,
   sets A0 to the literal 3-by-2 scalar matrix and v0 to (a*r,b*s,if real then r+s else t),
   and identifies the base with expMat(g,L*A0) and the response with expMat(g, planted
   L*v0 / prior-real / later-random columns). This is the exact algorithm identity needed
   by both column-law comparisons. Future proof must read mddhPreChallenge_eq,
   dlinChallenge_eq, expMat_apply, pow_val_mul/add and existing matrix-action transports;
   no scalar witnesses or arbitrary group inversion. This planning lemma is not yet
   syntactically consumed by the admitted comparison bodies: their eventual fills MUST
   use it (or those same public readers), so no completed dependency chain is claimed.
3. hRealClose: compares hybrid(j+1) acceptance with the AVERAGED actual redGame true,
   loss exactly 1/p^2. Consume the canonical dlin_real_column_gap_le at the actual public
   field, hPreScalar, scalar schedule transport, and existing coordinate resampling for
   the selected real S column. The other fixed masks form a bounded test of (M,v).
4. hRandomClose: compares hybrid(j) acceptance with AVERAGED actual redGame false,
   loss exactly 1-(1-1/p)^3. Consume dlin_random_column_gap_le at the actual public field,
   same algebra/casts and coordinate resampling for selected U column. This MUST use the
   canonical tuple law; it does not detour through fully uniform DLIN-matrix responses.
5. hLossBudget: arithmetic bound 1/p^2+[1-(1-1/p)^3]<=4/p, using orderSchedule_prime (p>=2).
   This is a named remaining arithmetic obligation, NOT asserted as already proved.
6. hCoinUnwrap: exact original reduction output verdict equals D.distinguisherL on mddhPre,
   at D coins transported from B with PUBLISHED NUPPT.coinsCongr hB.coins_eq. Consume
   dlinToMddh_eq, NUPPT.distinguisherL_eq/runAt_eq/runAt_coinsCongr/coinsCongr_ofFn,
   length_ofFn_coins and the list take-of-length law. The reduction is constrained only
   on layout-length coin lists, exactly as the existing RealizesOn reader specifies.

No new helper theorem proof is supplied. All six are local original-theorem subgoals, not
new weakened main statements. If a generic missing bridge emerges while filling them,
its exact header needs separate native reuse probes before any helper proof. Do not copy
private codec/probability/machine implementations into these holes.

## Drafted surrounding proof assembly (not yet natively checked)

- hEndpointGap uses mddhAdv_eq / advantage_eq and hEnds. Its d=0 consequence supplies
  the sentinel branch without any separate zero-dimension security assumption.
- hMeanComparison ACTUALLY applies abs_expect_sub_le_expect to the fixed-index tape average
  of redGame acceptance, then two public absolute triangle inequalities. The two exact
  column losses plus hLossBudget give avgTape(redGap)+4/p. No abstract closeness predicate.
- Positive hPointwise ACTUALLY calls exists_advantage_hybrid_gap and finite
  exists_expect_sample_le, scales by the nonnegative real d via div_le_iff_0 and
  mul_le_mul_of_nonneg_left, and finishes with mddhSlack_eq and mul_add.
- hCoinVerdict ACTUALLY applies RealizesOn.distinguisherL_eq and composes with the precise
  hCoinUnwrap obligation. B's coins are transported by coinsCongr with EXPLICIT machine
  arguments (A:=B)(B:=D), avoiding projection/implicit-machine inference ambiguity.
- hAccept ACTUALLY reads dlinGame_eq and the local redGame, then prob_bind/prob_pure.
  It reindexes D coins by expect_sample_equiv on coinsCongr, then rewrites hCoinVerdict.
  Foreign ProbComp.prob is never identified by semantic defeq.
- hGap uses dlinAdv_eq/advantage_eq/hAccept; the final bound substitutes it into hω.

## Mandatory public reuse routes for the comparison holes

The generic finite-field uniform image theorem and canonical column-law constants are
already in the import closure (SelfReduction imports ColumnLaws explicitly). Do NOT
re-prove rank/image/counting facts in hRealClose/hRandomClose.
At a fixed pp use public order_eq_of_publicParams and ZMod.ringEquivCongr to transport
uniform p-tapes to actual pp.group.order tapes, with expect_sample_equiv on canonical
finite coordinate maps / product equivalences. Fixed schedule is proof-only transport,
not an algorithm computing or hard-wiring a modulus.

For selected S/U columns, view each matrix as its column family through the public
Matrix.transposeAddEquiv and reuse ProbComp.expect_sample_update or expect_sample_coord
at j. Those theorems already prove that planting a fresh independent uniform coordinate
preserves the law; no local column-resampling counting argument should be authored.
Probability.expect_expect_sample exchanges the pp computation with the independent p-tape
average; expect_sample_comm / Bridge.expect_sample_pair handle finite independent factors.
The real branch's unused t and ignored tape coordinates use explicit expect_const.

The loss ledger is EXACT: real 1/p^2 plus random 1-(1-1/p)^3, rounded once to 4/p, then
multiplied by d. These already include zero a/b in canonical DLIN. dlinMatrixSlack does
NOT occur anywhere, and MUST NOT be added to this direct 4d/p theorem.

## Actual static reads/searches this invocation

Read CURRENT SelfReduction.lean advice/type/default/codec/readers and all preprocessor,
reduction, slack and frozen theorem sections; read current Defs MDDH game/sample readers,
Linear canonical DLIN sample/game/advantage/constructor readers and current ColumnLaws.
Confirmed current advice length/injectivity proofs are present; they are not re-proved here.

Actual rg searches covered hybrid/telescoping/gap, finite averaging, probability commuting/
resampling, shared RealizesOn coin/verdict readers, scalar/group exponent matrix actions,
and exact NUPPT coin equivalences. Broad outputs were truncated; all actually invoked
signatures were re-read in narrow ranges before drafting.
Exact nearest API declarations consumed/planned:
- Games/Advantage.lean:122 exists_advantage_hybrid_gap; :76 advantage_eq.
- Authentication/Signatures/Lamport/Averaging.lean:114 exists_expect_sample_le,
  namespace TCSlib.Cryptography.Authentication.LamportReduction (read namespace :39).
- Games/Probability.lean:409 abs_expect_sub_le_expect; :304 expect_sample_equiv;
  :325 expect_expect_sample; :353 expect_sample_update; :384 expect_sample_coord;
  :313 expect_sample_comm; :208/:224/:216 probability readers.
- Asymptotic/Realization.lean:108 RealizesOn.coins_eq; :115 runAtL_eq;
  :133 distinguisherL_eq; :145 runAt_coinsEquivPoly_symm (alternative typed route).
- Complexity/Randomized/PPT.lean:256 coinsCongr, :261 coinsCongr_ofFn,
  :268 runAt_coinsCongr, :171 coinLen_eq, :249 runAt_eq.
  IMPORTANT: this API is coinsCongr, NOT a guessed NUPPT.coinsEquiv; the exact signature
  was read and explicit source/target machine arguments are supplied in the candidate.
- Asymptotic/Adversary.lean:386 NUPPT.distinguisherL_eq.
- MatrixDH/Parameters.lean:160 order_eq_of_publicParams, :175 orderSchedule_prime,
  :181 orderSchedule_neZero; Data/ZMod/Basic.lean:419 ringEquivCongr and :459 val reader.
- Pairing/Exponents.lean:342 expMat_mulVec, :376 expMat_mul, :393 expMat_mul_left,
  plus published expMat/expVec coordinate and pow_val_add/mul readers.

An exploratory LinearSecurity/FixedPrime.lean path did not exist; actual shared public
parameter fixed-order transport was read instead. No conclusion relies on the missing
path or a private helper. No new helper requires a probe yet; the original M0 target was
already frozen. All local proof admissions remain explicit and must be filled later.

## Native-first checklist for this skeleton

First root should type this exact ladder with its six named sorries and inspect all errors.
Likely structural focus: dependent pp types in hybrid/hPreScalar, let Tape/avgTape finite
instance capture, cast fields, i.castSucc inference, exact endpoint/coin reindexing reader
application. The skeleton deliberately avoids a global classical command before the games;
Classical.choose is confined to noncomputable advice selection AFTER finite estimates.
No runtime native statement, helper, sampler or machine is built, and no completed proof
or standard-only security chain is claimed before all six holes and checks are resolved.
