# Small-row MDDH whole-proof candidate

Status: full scratch candidate, native elaboration / Rule 10 / axiom checks NOT RUN.
Only the lead may integrate and run Lean. Both FiniteLinear dependencies remain pending
native integration; this candidate therefore does not establish a standard-only theorem.

Candidate: MddhSmallRows.lean.inc (238 lines, one tactic block after comments are stripped).
The original live docstring and theorem header were copied byte-for-byte through the
`:=` marker from Pairing/MatrixDH/Defs.lean. No statement/prose repair was made.
MddhSmallRows.skeleton.lean.inc is retained as archived prior evidence, not overwritten.
No public helper, algorithm, runtime definition, sampler, machine, or import was created.
The existing local tests H/P/Q/good are preserved. Local hVerdict/hAccept are proof-only
assertions consuming the published probability/game readers; they are not new declarations.

## Dependencies and proof assembly

1. `expect_sample_matrix_mul_of_mulVec_surjective` is called with explicit
   K=ZMod pp.group.order, r=ell.eval kappa, m=2, c=d.eval kappa, M, its actual
   surjectivity hypothesis, and test H pp M. Its symmetric equality is hUniform.
   Its complete scratch proof is ExpectSampleMatrixMulSurjective.lean.inc.
2. `smallRows_surjectivity_failure_le` is called with the same explicit K,
   r=ell.eval kappa, and the EXISTING hypothesis hEll kappa. Its event probability
   is converted by explicitly instantiated prob_eq_expect, then core ite_not and
   ZMod.card; the resulting indicator inequality is hFailure. Scratch dependency:
   ../proofs-pairing/FiniteLinear/smallRows_surjectivity_failure_le.proof.lean.inc.
3. Local Fact pp.group.order.Prime and NeZero pp.group.order instances are explicit
   at all pp-bound range estimates, both helper calls, and the acceptance calculation.
   Matrix sample types and machine-coin predicates are explicit at bound/reader calls.
4. hEntry bounds the gap by zero on good bases and by one otherwise. The existing
   abs_expect_sub_le_expect reader averages it over the base matrix and then pp.
   Both averaging applications specify their f/g/h arguments.
5. hLoss reads publicParamsGen_eq, expect_bind/map, publicParamsCore_eq,
   PublicParams.group_eq and G.inst_eq. The expectation over the nonidentity
   generator draw is eliminated by ONE fully instantiated expect_const.
6. hAccept reads the ACTUAL mddhGame_eq/mddhSample_eq. At fixed pp/M/U,
   hVerdict uses explicit prob_eq_expect / prob_bind / prob_pure, keeping mddhEnc,
   expMat and D.distinguisherL opaque. It never uses semantic defeq of foreign
   ProbComp.prob. Only local H is reduced when presenting that leaf equality.
   The random branch integrates its unused coefficient matrix via an explicitly
   instantiated expect_const. The real branch integrates its unused uniform
   response matrix the same way, under a fixed coefficient matrix.
7. mddhAdv_eq and advantage_eq complete assembly. The final simp sees only four
   closed Bool/if readers, rather than recursively opening both whole games/tests.

The two finite-linear helpers are precisely the natively searched targets; no further
helper proof or helper API is proposed. No fixed-prime-schedule hypothesis, nonzero row/
column condition, or group-element scalar witness has been added. The same law applies
at ell=0 and d=0. The bound remains exactly 2/order averaged over G.gen.Coins.
This small-row bound does not add DLIN presentation slack to the direct 4d/p MDDH bound.

## Actual static searches and nearest reused APIs

Live root read: /Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange.
Read AGENTS.md and policy.md; no Lean/lake/Git/source edit/process operation was run.
Read Pairing/MatrixDH/Defs.lean (whole relevant game/readers and original theorem),
Pairing/MatrixDH/Parameters.lean:51-158, Games/Probability.lean:110-255 and :400-418,
and Pairing/Group.lean instance declarations.

Actual name/shape searches included:

- rg for expect_sample_matrix_mul_of_mulVec_surjective and
  smallRows_surjectivity_failure_le in TCSlib and /private/tmp/io-phfe-drafts.
  FiniteLinear.lean does not yet exist in the live root: a final targeted rg reported
  that absence, consistent with the parent's pending-integration status.
- rg for theorem prob_eq_expect / expect_const / prob_nonneg / prob_le_one /
  expect_nonneg / expect_mono / expect_bind / expect_map / prob_pure / prob_bind;
  and for publicParamsGen_eq / publicParamsCore_eq / group_eq / inst_eq.
- rg for Fact / NeZero / factPrime / order_prime / neZeroOrder in Group.lean:
  order_prime field :116; factPrime instance :167; neZeroOrder instance :170.
- rg for prob_map / prob_(map|bind|pure) and expectation map/bind shapes in
  Games/Probability.lean and Games/Bridges. No separate prob_map reader was found
  in this scope. The exact existing semantic leaf readers are Probability.lean
  prob_eq_expect :208, prob_pure :216 and prob_bind :224. Range readers are
  expect_const :174, expect_mono :193, expect_nonneg :202, prob_nonneg :230 and
  prob_le_one :236. Averaging is abs_expect_sub_le_expect :409.
- Searched ite_not in Mathlib/Logic, then actual core Init; nearest exact reader is
  lean4 v4.25.0 src/lean/Init/PropLemmas.lean:176. No conditional identity is re-proved.
- Searched ZMod card; exact reader is Mathlib/Data/ZMod/Defs.lean:164.
- Read Parameters readers group_eq :75, publicParamsCore_eq :137,
  publicParamsGen_eq :150 and Group.inst_eq :318. These are the only parameter
  representation readers used by hLoss; no public parameter algorithm is unfolded.
- Read the exact frozen prior skeleton and helper headers, the uniform-image full
  candidate, and the other agent's rank-failure candidate header. Read root's valid
  native-probe files/logs under evidence/search/mddh-finite-linear/run2; the exact?
  logs contain precisely their expected cannot-close diagnostics. Parent reported
  apply? produced partial suggestions only. The invalid run1 is NOT reuse evidence.
- Reused the opaque-probability leaf pattern from the separate DLIN ladder drafts;
  no proof of a generic probability lemma is duplicated here.

One first rg combined an escaped literal newline without -U and was rejected by rg before
searching. It was corrected with separate name/shape searches; no claim uses that failed
search. No runtime native search was run by this child.

## Static review only

After stripping Lean comments: exactly one `by` token, no sorry/admit/axiom/native_decide,
no public declaration except the frozen mddhAdv_smallRows_le, and no line over 100 columns.
There are 11 tactic metavariable goals (`:= ?_`) and 11 corresponding swap/bullet branches;
these are proposed tactic obligations, NOT verified discharged goals until native elaboration.
All foreign definitions are consumed by public readers; simp/rw lists contain local lets,
local equalities, or published theorem names only. No generated-equation reader is used.
The only unsatisfied external readiness condition is native integration of the two pending
FiniteLinear helper proofs/import. Main candidate elaboration may still require repairs;
this document asserts no PASS or completed standard-only dependency chain.

## Root diagnostic after this draft

Root confirmed that the concrete DLIN conversion hang was an unsolved synthetic
Field (ZMod pp.group.order) goal: Data.ZMod.Basic supplies the ring structure, while the
prime-field instance is declared in Mathlib.Algebra.Field.ZMod:23. Local Fact/NeZero
instances alone do not import that Field instance. Root is adding the precise Field.ZMod
import and preparing the official narrowed-cache/bootstrap route before native integration.
The earlier Fintype/classical-instance hypothesis was UNCONFIRMED and was not the actual
root cause. This candidate does not rely on that hypothesis. Its finite-linear helper calls
likewise need the actual Field.ZMod import available in the eventual import closure.
