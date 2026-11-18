# Backward-action decomposition: proposed helper statements only

The two exact proposed headers are in PrefixAlgebra.proposed.lean.inc. Their bodies are
scratch placeholders; no new helper proof has been written. probes.lean.inc repeats the
same statements anonymously, imports only Mathlib plus the core library-search tactic,
and does not import the named proposals. Run exact? and apply? separately on each target
before authorizing a proof. The agent ran no Lean/lake/Git or live edit.

## Independent home and size boundary

Suggested home: PartialGarbling/PrefixAlgebra.lean, namespace
PartialGarbling.PrefixAlgebra under the existing FunctionalEncryption root. All imports
are precise Mathlib modules. There is no dependency on Layered, Classes, Defs or another
TCSlib file, no new datatype or public definition, and no ABP representation. Layered can
import it without a cycle. The inline value in the second theorem is a mathematical
suffix sum in its statement, not an algorithm or new bundle.

The live Layered snapshot has 622 lines, now confirmed by the lead, leaving 378 lines
before the hard 1000-line cap. The earlier 760-line estimate was incorrect. The generic
helpers place dependent prefix indexing and suffix decomposition outside the source
module. Once proved, the remaining backward_action should be a reader bridge, two
matrix-block actions, the two helper applications, and ring cancellation, rather than
a large cast-heavy suffix proof. Measure the actual integrated proof as it develops;
there is currently no immediate size obstruction.

## The two helper contracts

prefixIncoming_sum is generic in an arbitrary node-value vector. Its left side sums the
value at each child whose explicit successor-depth node equals u. The child map covers
all nodes except the empty prefix exactly once. The right side is therefore zero at the
explicit root and value u elsewhere. Only an additive commutative monoid is needed.

prefixFlow_balance is the substantive weighted suffix identity. It defines value only
locally in its statement as the coefficient-weighted sum over all completions of a
prefix, using the same canonical tuple-length cast as the published Layered.extend_eq
reader. The outgoing weighted child sum plus the terminal coefficient sum equals value u.
It combines the nonterminal and terminal cases in one theorem, removing the need to
publish several source-specific cast, outgoing-fiber, terminal-value or suffix lemmas.
It is stated over a commutative semiring, because its suffix products and the edge-weight
reordering use commutativity; Layered specializes it to ZMod p.

Both contracts permit d=0 and an empty label type I. A zero-depth tuple has its unique
empty completion, the incoming/outgoing edge index is empty, and the terminal term
supplies the root coefficient. Neither theorem adds a positive dimension, prime,
nonzero-value, acyclicity, full-rank, or inhabitedness hypothesis. The existing prefix
index types themselves certify that every node depth is at most d. No mathematical
obstruction was identified. Typing and exact?/apply? results are intentionally pending.

## Searches and closest public reuse

Focused full-name and conclusion-shape searches over TCSlib, Mathlib and core found no
matching public prefix incoming-sum or weighted-prefix balance theorem. Commands and
outputs are in searches.txt. Existing readers and generic finite-sum laws must be reused,
not reproved inside either helper:

- Fintype.sum_sigma / sum_sigma', generated in Data/Fintype/BigOperators:144 and :152,
  split finite dependent edge/node sums by depth.
- Fintype.sum_ite_eq / sum_ite_eq', generated in
  Algebra/BigOperators/Group/Finset/Piecewise:288 and :293, collapse supported depths
  and tuples. Finset.sum_preimage and the existing fiberwise sum APIs provide alternative
  reindexing routes if an equivalence is cleaner.
- Finset.sum_fiberwise and Fintype.sum_fiberwise, generated in
  Algebra/BigOperators/Group/Finset/Basic:274 and :986, already provide generic fiber
  grouping. The proposed incoming theorem specializes the particular successor-prefix
  map and its missing root, not another generic fiberwise-sum proof.
- Sigma.mk.inj_iff and sigma_mk_injective, Data/Sigma/Basic:53 and :92, provide dependent
  pair equality/injectivity. Use them rather than rebuild sigma equality.
- Fin.snocEquiv, Data/Fin/Tuple/Basic:701, separates a last label and an initial tuple.
  Its pair order is (last label, initial tuple), and its forward map is snoc pair.2 pair.1.
  Do not accidentally assume the reverse pair order.
- Fin.consEquiv, Tuple/Basic:169, separates a first label and its tail; pair order is
  (first label, tail). Equiv.sum_comp, generated in Group/Finset/Defs:712, plus
  Fintype.sum_prod_type, Data/Fintype/BigOperators:253, reindex its finite sum.
- Fin.prod_univ_succ, Algebra/BigOperators/Fin:72, is already the first-factor product
  recurrence. Fin.prod_univ_zero:57 handles the empty completion. Do not inductively
  reprove these product formulas.
- Fin.append_right_cons and append_left_snoc, Tuple/Basic:658 and :653, provide exactly
  the prefix/suffix reassociation with its length cast. append_cast_left/right at
  :363/:368 and core Fin.cast_cast / Fin.cast_refl resolve the remaining length casts.
  No new generic append or cast lemma is proposed.

The earlier optional weightedCons_sum target can be omitted if prefixFlow_balance is
proved directly by these existing tuple/sum/product APIs. No separate new generic
finite-function splitting theorem is required merely to fill this proof.

## Layered.backward_action after the generic proofs

Specialize I=Fin(l+1), R=ZMod p, weight=xhat x and
c tau = sum j, C j tau * z j. Then:

1. Identify the local generic value with Layered.backward C x z using backward_eq and
   extend_eq, plus beta reduction. This is a reader bridge, not exponent extraction.
2. Read matrix_inl and the output rows from matrix_eq, L1_inr and L0_inr. Use the existing
   Matrix.sumElim_vecMul_fromRows (ColumnRowPartitioned:189) if arranging this as a block
   matrix, together with shift_inl/shift_inr. Do not reprove a block action.
3. PathAlgebra.weightedIncidence_vecMul gives outgoing minus incoming. Its multiplication
   order flow*weight matches prefixFlow_balance exactly.
4. The output block is the terminal sum in prefixFlow_balance. The required exchange of
   its j/tau sums uses Finset.mul_sum, Finset.sum_comm and conditional multiplication.
   Reorder C*z versus z*C only in the commutative residue ring. No new output-row helper
   is needed if these existing readers and generic sum laws fit inline.
5. Apply prefixIncoming_sum and prefixFlow_balance. At the root the incoming sum is zero;
   away from it the incoming value cancels the node's suffix value. root_eq identifies
   the distinguished source, and the already completed backward_root gives z dot f(x).

The theorem's frozen header and statement prose are unchanged. Correctness rec_spec is
independent of this harder security-side path calculation; its supplied proof uses only
forward_action and garbling/reconstruction readers.
