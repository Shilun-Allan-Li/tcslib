# BilinearGen.dlinMatrixGame_real_accept candidate

Status: independent scratch candidate, checked by inspection only; native pending. No Lean,
lake, build, Git, live edit, new sampler, or extra agent was used. Exact live name is
 dlinMatrixGame_real_accept. Frozen prose/header byte-preserved; one tactic block, no
remaining holes/sorry, no helper/import/statement change; all lines ≤100 columns.

## Actual live statement and dependency clarification

The live matrix experiment is already COMPRESSED: dlinMatrixSample_eq explicitly returns
ar, bs, r+s in its real branch, rather than constructing dlinMatrix*vector. Therefore the
existing dlinMatrix_mulVec candidate remains native pending but is NOT a dependency of this
acceptance equality. The frozen sketch names that elementary theorem; the concrete raw
reader has already encoded its coordinate result, so this proof can directly compare the
two laws. This route discrepancy is disclosed for root's proof-sketch audit; no frozen prose
or statement was changed and no artificial unused lemma dependency was introduced.

## Existing probability APIs suffice

The public group, generator, ab, rs and distinguisher coins are literally the same draws in
both reader expressions. dlinMatrixSample also draws u:Fin 3->ZMod p, while dlinSample draws
t:ZMod p. In the real branch both are unused. Read accept/game/sample equations, total
probability, total expectation and pure-return readers. The standard reduceIte simproc
reduces the closed real-branch condition. ProbComp.expect_const integrates out u and t,
independently of their different types. Both expressions then agree exactly.

No uniform sample equivalence is needed because no used random variable is reindexed.
No computation equality is claimed: these syntax trees have different unused queries, so
it is their acceptance law (the frozen target) that is identified. No new fixed-parameter
law helper, sampler construction, or private proof copy is necessary.

## Actual reuse searches and exact APIs

* Read Pairing/Linear.lean:185-368 for dlinSample_eq (202), dlinGame_eq (219),
  dlinMatrixSample_eq (267), dlinMatrixGame_eq (289), and frozen target (322).
* Searched sample equivalence/product/map APIs in Games/Probability.lean and Foundations/
  Probability.lean, then Games/Foundations. Located expect_sample_equiv (304) and
  expect_sample_comm (313); inspected them. Neither is required for unused draws.
* Read Games/Advantage.lean:1-110: accept_eq (64) is the published probability reader.
* Read Games/Probability.lean:105-173, :175-230, :263-328. Exact readers used:
  expect_pure (117), expect_bind (128), expect_const (174), prob_pure (216), prob_bind (224).
* Searched expect_congr/expect_const/expect_pure/prob_bind/prob_pure/expect_bind in the
  shared probability/advantage modules and Pairing files. No new congruence lemma needed.
* Read nearby Pairing/Assumptions.lean:327-340 for established use of the standard
  `↓reduceIte` simproc with these same public probability readers. No private proof is
  transcribed or referenced; that existing private probability bound concerns different
  games and an equivalence of adversary coins.
* A Fin2/tuple equivalence search located finTwoArrowEquiv; it is irrelevant here because
  the used ab/rs draws already have identical types and coordinates in both experiments.

Every explicit simp item is a published reader or the existing closed-conditional simproc;
no foreign/core/Mathlib definition or generated equation is passed to simp/rw/unfold.
No group representation, scalar witness, encoder or setup sampler is changed.

Native focus: recursive probability/expectation simplification under the dependent public
parameter binder and cancellation of both constant unused-draw expectations. Mathematically
all conditions are covered by existing finite nonempty scalar samples.
