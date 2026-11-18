# Layered.matrix_inl: next forward-action prerequisite

The lead identified an existing forward_node draft from the FE agent at
`/private/tmp/io-phfe-drafts/proofs-fe/LayeredForwardNode.lean.inc`. It was read rather
than duplicated. Accordingly this invocation supplies exactly one proof: matrix_inl,
the previously proposed and natively searched incidence-row helper.

`Layered.matrix_inl.proof.lean.inc` preserves the searched header and opening statement
prose. Only its sketch is refreshed to name the abstract padded-incidence identity.
It has 19 lines, maximum width 81, one tactic block and no admission. Insert immediately
after matrix_eq in Layered, inside the existing Algorithms section and variables.
No live edit, Lean/lake, Git, proof check or new agent was used; root validation is pending.

## Required native reuse searches

The exact matrix_inl statement occurs in the root's checked
`.lake/io-phfe-probes/LayeredHelpersReuse2.lean`:243-248. Its exact? search did not close
the goal. The apply? search found only partial suggestions. Raw logs read:

- evidence/search/path-algebra/run2/mods/.lake_io-phfe-probes_LayeredHelpersReuse2.log;
- evidence/search/path-algebra/run2/mods/.lake_io-phfe-probes_LayeredHelpersApply2.log.

The root's prefix probe has earlier M0 admissions for count/coordinate laws; this candidate
does not use them. Focused source searches are in `Layered.matrix_inl.searches.txt`.

## Exact dependency and Rule 10

The proof evaluates `PartialGarbling.PathAlgebra.paddedIncidence_eq` at the selected
TIdx/MIdx coordinates. That helper's proof is now present in live PathAlgebra; its native
validation status was not independently established by this agent. This bridge explicitly
depends on that helper, so its final axiom census must follow the helper's completed check.
It is independent of forward_root, backward_root, forward_node and both incidence-action
helpers. It introduces no further helper or source assumption.

The remaining normalization uses only published readers:

- Layered.matrix_eq:226, L1_inl:190, L0_inl:209;
- PartialGarbling.Defs.publicTensor_apply:75;
- Classes.xhat_eq:75;
- Mathlib Matrix.of_apply, LinearAlgebra/Matrix/Defs:83, add_apply:216;
- Mathlib Matrix.mul_apply, Data/Matrix/Mul:293;
- Mathlib Fintype.sum_prod_type, Data/Fintype/BigOperators:251-256.

Splitting the product sum makes the L1/publicTensor coordinate readers apply to explicit
(i,node) pairs. Both sides then have identical scalar sums. Every simp argument is a
reader or public theorem. No TCSlib definition body is unfolded or reduced, and no
singleton-sum, padded-incidence, or block-matrix proof is repeated inline.

Layered already imports PathAlgebra and the precise product-sum module. This proof needs
no new import and does not depend on ColumnRowPartitioned, though checking the whole file
will of course require its existing import cache to be available.

## Plan for the next existing M0 theorem: forward_action

Once matrix_inl and the already supplied forward_node are installed:

1. On an auxiliary row, use PathAlgebra.weightedIncidence_mulVec for parent/node maps
   with weight `xhat x (lastLabel v)` and values `forward x`. The existing forward_node
   recurrence and one multiplication-commutativity equation cancel its result to zero.
   This avoids another singleton-sum calculation in the source module.
2. For the output rows, read matrix_eq, L1_inr and L0_inr. The variable contribution
   vanishes using existing zero/sum laws. Expand the coefficient sum with Finset.sum_mul,
   interchange the node/tuple sums with Finset.sum_comm, and use Fintype.sum_ite_eq' at
   each fixed leaf. Then leaf_eq, forward_eq and polyTensorEval_eq give the output value.
3. Matrix.fromRows_mulVec (Data/Matrix/ColumnRowPartitioned:180) supplies row-block
   splitting if the proof is arranged as a block equality. Otherwise extensionality
   followed by Sum cases uses the same two existing reader calculations. Do not reprove
   a block-matrix action lemma.

No new helper is proposed or proved for the output case. A leaf-injectivity lemma is
unnecessary: each fixed monomial tuple selects exactly its supplied leaf coordinate.
The entire route handles p=1 and l/n/d=0; no positivity or rank hypothesis is added.
No mathematical obstruction was found.
