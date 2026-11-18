# Layered.forward_action proof candidate

Exactly the existing M0 forward_action body is replaced in the scratch fragment.
The live header and entire docstring, including statement prose and proof sketch, are
preserved byte for byte. The fragment contains one tactic block, no admission, and no
new helper. No matrix_inr helper is needed or proposed. No live edit, Lean/lake, Git,
proof checker or new agent was used; the lead must validate the candidate.

## Dependency list

- `PathAlgebra.weightedIncidence_mulVec`: proved and natively PASS according to the lead.
- `Layered.forward_node`: proved and natively PASS according to the lead.
- `Layered.matrix_inl`: the previously searched/queued bridge; its native completion must
  precede the final proof/axiom census. Through this bridge the proof depends on
  `PathAlgebra.paddedIncidence_eq`, which the lead reports PASS.
- Existing proved readers: matrix_eq, L1_inr, L0_inr, leaf_eq, forward_eq,
  Classes.polyTensorEval_eq, and the public Mathlib coordinate/sum laws listed below.

The proof does not depend on forward_root, backward_root, backward_action, rec_spec,
translation, privacy, nodeBound_eval, auxCount_add_one or nodeCoord_root. Thus no remaining
M0 source admission is silently consumed, apart from the disclosed matrix_inl checkpoint
if it has not yet been natively completed.

## Proof and exact reuse

Auxiliary rows use the completed abstract incidence action at one TIdx coordinate.
`Matrix.mulVec_eq_sum` (Data/Matrix/Mul:697) is the published coordinate-sum reader;
`Finset.sum_apply` (generated in Algebra/BigOperators/Pi:40-43), `Pi.smul_apply`,
`Matrix.transpose_apply` (LinearAlgebra/Matrix/Defs:134), `Matrix.of_apply` (:83), and
`op_smul_eq_mul` (Algebra/Group/Action/Defs:71) identify its left side with the actual
row using matrix_inl. forward_node and multiplication commutativity make the difference
zero. mul_comm is used only over the commutative residue ring, not in an abstract ring law.

Output rows use the same public mulVec coordinate reader, then matrix_eq,
Matrix.add_apply (:216), Matrix.mul_apply (Data/Matrix/Mul:293), L1_inr and L0_inr.
The variable row is zero by zero_mul and Finset.sum_const_zero. The only subsequent
finite-sum steps are existing public results:

1. `Finset.sum_mul`, Algebra/BigOperators/Ring/Finset:49;
2. `Finset.sum_comm`, generated in Algebra/BigOperators/Group/Finset/Sigma:117;
3. `Fintype.sum_ite_eq'`, generated in Group/Finset/Piecewise:292-295, after ite_mul
   and zero_mul expose the supported term.

The singleton sum is over nodes at a fixed tuple, so leaf injectivity is unnecessary.
leaf_eq and forward_eq turn its selected value into the full padded monomial;
`Fin.val_last` (core Init/Data/Fin/Lemmas:284) reads the terminal depth; the existing
polyTensorEval_eq reader identifies the final coefficient sum.

All simp/rw arguments are theorem readers or algebra laws. No TCSlib definition is
unfolded, and no finite-sum, coordinate-action, or block-matrix result is reproved.
`change` reduces only the core Sum.elim applications at Sum.inl/Sum.inr. The proof uses
ordinary Sum case analysis rather than constructing a block matrix and reproving its
matrix-action theorem. It needs no additional import beyond the live Layered imports.

Focused source name/conclusion searches and exact lemma locations are saved in
`Layered.forward_action.searches.txt`. This is a proof of an existing source theorem,
not a new helper claim; no new unprobed helper is smuggled into a local have. The local h
is precisely congrFun applied to the already searched/proved incidence theorem.

All dimensions may be zero and p may be 1. No rank, nonzero, prime or positivity condition
is added. No mathematical obstruction was found.
