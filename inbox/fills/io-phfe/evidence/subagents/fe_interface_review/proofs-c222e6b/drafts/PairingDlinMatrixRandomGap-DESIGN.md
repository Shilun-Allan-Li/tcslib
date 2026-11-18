# Pairing.dlinMatrixGame_random_gap_le: exact helper proposal and proof design

Status: DESIGN / SEARCH REQUEST ONLY. No proof of the new helper or frozen main theorem was
written. No Lean/lake/build/Git/live edit/extra agent was run. The frozen main theorem is
copied with its original admission in PairingDlinMatrixRandomGap.frozen-header.lean.inc;
its exact name is dlinMatrixGame_random_gap_le, not dlinMatrix_random_close. All proposed
helper statements remain scratch, unintegrated and native-unverified. No claims of pass.

## Necessary new target for native exact?/apply? searches

PairingDlinDiagonalRandomGap.target.lean.inc proposes ONE fixed-field probability lemma:
for an arbitrary bounded test H:(Fin2->K)->(Fin3->K)->Real over a finite field K, compare

  E_ab E_u H ab u

with

  E_ab E_rs E_t H ab ![ab0*rs0,ab1*rs1,t].

The exact gap bound is 2/N - 1/N² for N=card K. This target contains the complete random-law
scalar correction, not an undefined 'close' assumption or a weaker 2/N union bound. It is
independent of group encodings, adversary machines and samplers. Its natural home is
Pairing/Linear.lean in namespace Pairing, near dlinMatrix_mulVec and before BilinearGen.
The field/test quantification is exactly what the pointwise public-parameter argument
needs; no general statistical-distance interface is introduced.

The source searches below found all component APIs but no complete finite-field bounded-
test inequality. Root must first run prefix-only exact?/apply? probes. The machine-readable
request identifies the target, prospective API imports and valid source prefix. Do not
include this proposed admitted target, later random-gap theorem, or later Linear admissions
in the probes. No helper proof is supplied before those searches.

## Concrete fixed-field proof obligations (for a later invocation after probes)

1. Let A(ab)=E_u H ab u and B(ab)=E_rs E_t H ab [ab0*rs0,ab1*rs1,t]. Existing expect_nonneg,
   expect_mono and expect_const give 0≤A,B≤1 from the supplied hH0/hH1.
2. On good(ab):ab0≠0∧ab1≠0, prove A(ab)=B(ab) using exactly existing equivalences:
   * Equiv.mulLeft₀ (ab i) hi is multiplication by the known nonzero diagonal coordinate.
   * Equiv.piCongrRight combines the two coordinate permutations. Fin2 case analysis only
     proves each supplied hi; it does not define a new sampler or matrix algorithm.
   * Fin.succFunEquiv K 2 (inverse direction) identifies (Fin2->K)×K with Fin3->K.
   * expect_sample_equiv and Bridge.expect_sample_pair transport the two used uniform draws.
   Published finite tuple readers identify the three coordinates. No arbitrary group point
   is inverted or assigned a scalar witness.
3. Thus |A(ab)-B(ab)|≤if ab0=0∨ab1=0 then1else0: use the exact good equality off bad and
   [0,1] bounds on bad. Apply abs_expect_sub_le_expect to sample(Fin2->K).
4. Evaluate the remaining EXPECTATION OF THE BAD INDICATOR exactly, rather than union-bound
   it: finTwoArrowEquiv K and existing sample/Fubini readers convert ab to two independent
   K draws. For c=1/N, the inner bad probability is 1 when a=0 and c otherwise. Rewrite it
   as c+(1-c)*1_{a=0}; the outer expectation is c+(1-c)*c=2/N-1/N².
   Reuse OneWay.uprob_eq_one_div_card 0 via Bridge.prob_sample_eq_uprob for each singleton
   event, plus existing expect_add/expect_const_mul/expect_const. Do not prove a private
   singleton counting or generic union/intersection lemma. Field nonemptiness ensures N≠0;
   field_simp/ring finish the rational identity. No second helper target is currently needed.

## Exact main-theorem assembly after the helper is proved

1. Read accept_eq, the two game/sample readers, prob_bind/expect_bind and pure-return readers.
   In the matrix false branch the rs draw is unused and is eliminated by expect_const.
2. For each actual pp, instantiate K=ZMod pp.group.order. BilinearGroup.factPrime already
   supplies its Field instance; ZMod.card identifies N with pp.group.order. Define only a
   local test expression

   H ab u = ProbComp.prob (ProbComp.sample (D.Coins κ))
     (fun r => D.distinguisherL κ
       (G.dlinEnc κ (G.dlinChallenge κ pp
         (g^(ab0).val) (g^(ab1).val)
         (g^(u0).val) (g^(u1).val) (g^(u2).val))) r = true).

   Existing prob_nonneg/prob_le_one give hH0/hH1. The helper's two expectations match the
   normalized actual false games, with the original base metadata ab retained in H.
3. Apply abs_expect_sub_le_expect to the COMMON publicParamsGen G κ draw, with pointwise
   loss 2/order(pp)-1/order(pp)^2. No fixed modulus schedule is assumed or computed.
4. To identify the averaged loss with dlinMatrixSlack, read publicParamsGen_eq, expect_bind,
   expect_map and publicParamsCore_eq. The loss depends only on the description, so the
   additional uniform nonidentity-generator expectation is constant and integrates out.
   Read G.inst_eq to replace group κ (G.desc κ ρ) by G.inst κ ρ, then dlinMatrixSlack_eq.
   This explicitly preserves the raw generator-coin law even when different coins give the
   same description; no injectivity of desc or illicit dependent-sum sample is assumed.

The frozen target and slack are unchanged. dlinMatrix_mulVec is native pending but, as in
real-law equality, is not an actual dependency of the already-coordinate-expanded false-law
reader. All new work is fixed scalar-field probability, not matrix/group scalar recovery.

## Actual searches / exact nearest reusable APIs

Read Pairing/Linear.lean:304-352 for the exact slack and frozen target/prose.

* Games/Probability.lean: expect_sample (147), expect_const (174), expect_mono (193),
  expect_nonneg (202), prob_nonneg (231), prob_le_one (236), prob_congr (254),
  expect_sample_equiv (304), expect_sample_comm (313), expect_expect_sample (326),
  expect_sub (340), abs_expect_sub_le (393), abs_expect_sub_le_expect (409).
  Read :365-453 and searched bad/event/abs/expect/prob families. No arbitrary bounded-test
  'agree off bad' lemma was found, but abs_expect_sub_le_expect is precisely sufficient.
* Games/Hopping.lean: prob_split (76), abs_prob_sub_le_of_agree (126). Read exact types:
  these compare EVENTS on one common computation, not arbitrary conditional expected tests
  on differently reindexed response draws. They are nearest alternatives, not a direct
  completion of this target. No Games.Closeness import is proposed or used.
* Games/Bridges/Experiments.lean: prob_sample_eq_uprob (66),
  expect_sample_eq_uexp (74), expect_sample_pair (80), prob_sample_pair (89). Read :51-87.
* OneWayFunctions/Basic.lean:144, OneWay.uprob_eq_one_div_card. Read :136-152. This published
  singleton probability theorem avoids a new private counting proof. Its precise import and
  Bridges/Experiments may need adding if not already in the current closure; root decides.
* Mathlib/Algebra/GroupWithZero/Units/Equiv.lean:30, Equiv.mulLeft₀; :34,
  mulLeft_bijective₀; :39, Equiv.mulRight₀. Read :19-49. This is known scalar-field
  multiplication; no group logarithm/inverse-encoding API is used.
* Mathlib/Logic/Equiv/Basic.lean:147, Equiv.piCongrRight. Read its existing construction.
* Mathlib/Logic/Equiv/Fin/Basic.lean:48, finTwoArrowEquiv; :406, Fin.appendEquiv;
  :415, Fin.succFunEquiv. Read the exact source shapes and existing simps declarations.
* Mathlib/Data/ZMod/Defs.lean:164, ZMod.card. Pairing/Group.lean:166-170,
  BilinearGroup.factPrime/neZeroOrder. These supply the field/cardinality instantiation.
* Inspected Mathlib/Data/Fintype/Card.lean:380 (card_subtype_compl) as a counting alternative;
  it is unnecessary when the existing singleton probability theorem is reused.

Search commands used semantic rg patterns for sample equivalence/product/map, bad-event /
expectation bounds, field multiplication equivalences, fixed Fin2 zero-event laws and singleton
probability. A broad intermediate output was truncated, then exact smaller source ranges were
read. No private proof from any other consumer is copied or invoked.

## Pending / honest limits

Requested native records for the new helper: exact?=NOT RUN, apply?=NOT RUN, statement typing=
NOT RUN. No helper proof or main proof is supplied in this invocation. No mathematical
obstruction was found: the exact bound follows from the above concrete good-law and bad-mass
obligations. Remaining work is substantive finite probability algebra and API elaboration,
not an unrecorded premise, abstract secure-to-secure bridge or a weakened slack.
