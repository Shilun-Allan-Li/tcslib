# Cycle-free PathAlgebra fallback: proposed headers only

Three primary headers are in `PathAlgebra.proposed.lean.inc`; their bodies are deliberate
scratch placeholders, not supplied proofs. `probes.lean.inc` repeats the exact statements
as anonymous examples without importing or declaring the named helpers. No Lean, lake,
Git, live edit, proof check, or new agent was used. All proposed Lean lines are at most
88 columns, and no candidate contains a tactic block.

The intended new public home is:

`TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/PartialGarbling/PathAlgebra.lean`

The namespace is `PartialGarbling.PathAlgebra` under the existing FE root. Its only imports
are precise Mathlib modules. It imports neither Layered, PartialGarbling.Defs, Classes nor
any other TCSlib module. Thus the dependency direction is Mathlib → PathAlgebra → Layered,
without a cycle. There is no ABP or graph datatype, no definition, and no algorithm or
sampler in the proposed file.

## Primary proposed API

1. `weightedIncidence_mulVec`: the row with weight w at its parent and -1 at its child
   sends a node vector a to w*a(parent)-a(child). Only the summed node type must be finite.
2. `weightedIncidence_vecMul`: the same matrix sends an edge-flow vector to the outgoing
   weighted-flow sum minus the incoming-flow sum at every node. Only the summed edge type
   must be finite.
3. `paddedIncidence_eq`: the abstract variable-incidence matrix times the abstract
   public-input tensor, plus the constant-edge/negative-child matrix, is exactly the
   weighted endpoint matrix whose edge weight is `Fin.snoc x 1 (label e)`.

The first two use an arbitrary ring, including a noncommutative or trivial ring. The
multiplication order is intentional: forward is weight*value; backward is flow*weight.
Layered uses a commutative residue ring and its existing forward_node orientation is
value*weight, so that specialization needs one explicit commutativity equation. No theorem
requires injectivity, distinct endpoints, acyclicity, a root, a nonzero weight, a field,
positive dimensions, or inhabited finite types. Repeated endpoints and loops are handled
by subtraction. These are genuine algebraic facts, not security or path hypotheses.

The padded formula permits l=0; its sole padded label has weight 1. An empty node type
causes no problem: any supplied endpoint map determines the corresponding empty edge
case. The optional weighted-cons target also permits an empty label type and k=0.

## Required root-only probes

Run `exact?` and `apply?` separately on each of the three examples in `probes.lean.inc`,
using the approved checking route after the active census. Replace one placeholder at a
time and retain both suggestions and unresolved goals. Do not import the proposed named
headers while searching: their placeholder bodies would make the search circular.
The proof-search import is the core `Lean.Elab.Tactic.LibrarySearch`.

Text searches found no existing full name or direct parent/child, weighted-incidence,
padded-incidence, or Fin.snoc/matrix-action conclusion. The exact commands and outputs
are in `searches.txt`. This is not a substitute for the required exact?/apply? probes.

## Nearest public reuse and duplication boundary

- Mathlib `SimpleGraph.incMatrix`, Combinatorics/SimpleGraph/IncMatrix:54, is an unsigned
  vertex-by-`Sym2` matrix. The module identifies itself as unoriented at line 13 and lists
  oriented incidence as future work at lines 39-41. It cannot express these arbitrary
  weighted parent/child rows without an unnecessary graph construction. Its product
  formulas at lines 110, 134 and 167 concern incidence/transpose products, not either
  action here. Do not import graph modules merely to obtain this mismatch.
- `SimpleGraph.adjMatrix_mulVec_apply`, SimpleGraph/AdjMatrix:195, sums neighboring values.
  `SimpleGraph.lapMatrix_mulVec_apply`, SimpleGraph/LapMatrix:59, is degree times the node
  value minus its unweighted neighbor sum. Neither states the arbitrary weighted directed
  endpoint row or its edge-flow action.
- `Matrix.single_dotProduct`, Data/Matrix/Mul:178, and `single_one_dotProduct`:205, already
  evaluate a row supported at a single coordinate. `sub_dotProduct`:225 and
  `sub_mulVec`:1007 already distribute subtraction. The proposed forward theorem must
  compose these existing statements after identifying its rows with two `Pi.single`
  vectors. It must not reprove singleton-product sums, matrix subtraction, or linearity.
- `Matrix.single_mulVec`, Data/Matrix/Basis:100, acts by a matrix with one nonzero entry
  and produces a coordinate update. It is a close relative but has one fixed row/column,
  whereas our row supports vary with e. It need not be imported if the shorter
  `single_dotProduct` route suffices.
- `Matrix.vecMul_sub`, Data/Matrix/Mul:1010, already distributes the backward subtraction.
  Existing `Finset.sum_sub_distrib`, `ite_mul`, `mul_ite`, and elementary multiplication
  equations can put its two finite sums into the proposed displayed form. No new generic
  finite-sum or conditional-multiplication lemma should be introduced.
- `Fintype.sum_prod_type`, Data/Fintype/BigOperators:251-256, splits the padded formula's
  Fin-l-by-node sum. `Fintype.sum_ite_eq'`, generated at Group/Finset/Piecewise:292-295,
  collapses the matching node coordinate. `Fin.lastCases` plus `Fin.snoc_castSucc`:506 and
  `Fin.snoc_last`:519 in Data/Fin/Tuple/Basic separate variable and constant labels.
  The padded theorem packages this coordinate contraction, not a replacement proof of
  any of those public primitives.
- Matrix wrapper and arithmetic readers are `Matrix.of_apply`, LinearAlgebra/Matrix/Defs:83,
  `add_apply`:216, `sub_apply`:224 and `mul_apply`, Data/Matrix/Mul:293. Use these readers;
  core/Mathlib reduction in a `show` or `rfl` is permitted, but no definition is to be
  passed to simp, rw or unfold.

The nearest algebra results are deliberately reused. These proposed theorems are named
compositions for a particular endpoint-matrix shape; none supplies a new singleton,
product-index, or block-matrix proof. If exact?/apply? produces a direct public theorem,
use it instead and omit the corresponding proposal.

## Existing block APIs: do not add duplicate wrappers

Mathlib Data/Matrix/ColumnRowPartitioned provides:

- `Matrix.fromRows_apply_inl`:52 and `fromRows_apply_inr`:56;
- `Matrix.fromRows_mulVec`:180;
- `Matrix.sumElim_vecMul_fromRows`:189 and `vecMul_fromRows`:196.

These already split edge/output row blocks exactly. Layered should import the precise
module if it is not already available and use these theorems directly. No proposed new
block-incidence theorem is needed. Output leaf sums can use existing `sum_dotProduct`
(Data/Matrix/Mul:147), `single_dotProduct`, and singleton-sum equations; avoid a new
leaf-injectivity lemma, because each fixed tuple contributes at exactly its supplied leaf.

## Layered specialization and size plan

Specialize V=MIdx l d, E=TIdx l d, R=ZMod p, parent=Layered.parent, child=Layered.node,
label=Layered.lastLabel. The padded theorem absorbs the long matrix_inl contraction.
The only TCSlib-specific reads in its Layered bridge are matrix_eq, L1_inl, L0_inl,
publicTensor_apply and xhat_eq. Each matrix expression can then be compared through the
public entry equations. The bridge must not unfold these definitions.

For forward_action, split off the output rows with `fromRows_mulVec`, use the weighted
forward theorem and the separately proposed forward_node recurrence. For backward_action,
use `sumElim_vecMul_fromRows` and the weighted backward theorem with flow v equal to
backward C x z (node v). The source-specific remaining work is the suffix recurrence and
identifying each node's incoming child edge; keep that combinatorics beside the Layered
definitions.

This moves the generic padded-matrix contraction and both incidence-action calculations
out of the current 493-line module. It is the useful fallback for the 1000-line hard cap,
rather than placing only a tiny product lemma in a new file. The actual savings depend
on proof layout, so no checked final length is claimed. Continue measuring while filling
backward_action; do not wait until the file exceeds 1000 lines.

## Optional next probe if suffix algebra is still too large

`optional-weighted-cons-probe.lean.inc` contains only an anonymous exact statement for
factoring a weighted finite-function sum into first label and tail. No named declaration
or proof is proposed for immediate integration. Its existing building blocks are
`Fin.consEquiv.sum_comp`, `Fintype.sum_prod_type`, `Fin.prod_univ_succ`, `Fin.cons_zero`,
`Fin.cons_succ`, distributivity and commutativity. Existing TCSlib consumers of the
finite-function reindexing appear in Products/Tensorization:80-85 and
Complexity/Randomized/RandomWalkMixing:196. Their local subproofs should not be copied.

This optional theorem needs its own exact?/apply? probes. Mathlib already supplies
`Fin.append_left_snoc` and `Fin.append_right_cons` at Tuple/Basic:653-661, including the
length cast; do not introduce or reprove those reassociation facts. No mathematical
obstruction has been found in the primary or optional statements.
