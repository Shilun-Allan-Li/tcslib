# Layered.backward_action proof candidate

Exactly the existing theorem body is supplied. Its frozen header and entire docstring
are byte-for-byte unchanged in Layered.backward_action.proof.lean.inc. The fragment has
85 lines, maximum width 88, one tactic block, no admissions and no new public helper.
The four local tactic side-goals use the lead's explicit swap/filling-bullet pattern.
Each ?_ is filled in the same fragment, not left as an admission.

The agent ran no Lean, lake, Git, live edit or proof checker. Native elaboration and a
final axiom check are pending; this is not a standard-axiom-only certification of the
new backward_action body.

## Dependency status

The lead now reports native PASS for all three PrefixAlgebra helpers, including the
completed terminal and nonterminal prefixFlow_balance proof. The earlier flow dependency
is therefore no longer pending. Direct new-theorem dependencies are:

- PathAlgebra.weightedIncidence_vecMul;
- PrefixAlgebra.prefixFlow_balance;
- PrefixAlgebra.prefixIncoming_sum;
- Layered.matrix_inl and Layered.backward_root.

The flow theorem depends in turn on prefixOutgoing_sum. These prerequisites are all
reported native PASS by the lead. The candidate uses the existing proved matrix,
shift, backward and tuple-extension readers below. It consumes no forward_action,
rec_spec, translation, privacy, node-count or coordinate admission.

## Exact reuse and source-specific reader bridges

The local edges/outputs matrices are mathematical abbreviations in this proof, not new
public definitions or algorithms. hMatrix reads the source matrix at its two row kinds:
Matrix.fromRows_apply_inl/inr (Mathlib Data/Matrix/ColumnRowPartitioned:52/:56) expose
those rows; matrix_inl supplies the edge entries; matrix_eq, Matrix.add_apply,
Matrix.mul_apply, L1_inr and L0_inr give the terminal coefficient entries.
No generic block-matrix theorem is reproved by this source-specific identification.

hShift combines shift_inl/shift_inr with the existing core Sum.elim_comp_inl_inr
(Init/Data/Sum/Lemmas:122) and function congruence. It does not reprove generic Sum eta.
The actual action split is exactly Matrix.sumElim_vecMul_fromRows
(Data/Matrix/ColumnRowPartitioned:189). The edge action then comes directly from
PathAlgebra.weightedIncidence_vecMul, with flow v=backward C x z (node v) and edge
weight xhat x (lastLabel v). Its flow*weight multiplication order already matches
prefixFlow_balance.

For the terminal block, hOutput uses the published Matrix.vecMul_eq_sum
(Data/Matrix/Mul:694), then Finset.sum_apply, Pi.smul_apply and smul_eq_mul. The only
finite-sum algebra is the existing Finset.mul_sum, Finset.sum_comm and
Finset.sum_ite_irrel (generated at Algebra/BigOperators/Group/Finset/Defs:550).
The conditional-sum law is used directly, not reproved by cases. mul_comm changes
z*C into C*z in the commutative residue ring. The result is exactly the terminal sum
in prefixFlow_balance, so no leaf-injectivity or terminal-vector helper is needed.

hBalance specializes prefixFlow_balance with I=Fin(l+1), R=ZMod p,
c tau=sum j C j tau*z j and weight=xhat x. parent_eq, node_eq, lastLabel_eq and leaf_eq
identify its explicit tuple maps. backward_eq and extend_eq identify its local generic
suffix value with the source backward function. This is a reader-only specialization;
no suffix recurrence, tuple reindexing or cast proof is repeated.

hIncoming specializes prefixIncoming_sum to the backward node vector. Only node_eq and
root_eq are needed; the arbitrary value vector remains opaque. Finally the existing
sub_add_eq_add_sub (generated from Algebra/Group/Basic.div_mul_eq_mul_div:547) rewrites
(outgoing-incoming)+terminal into (outgoing+terminal)-incoming. The two helper equalities
then cancel every non-root column. At the source, backward_root supplies z dot f(x).

## Rule 10 and boundary

Every simp/rw entry is a theorem, published reader or local proved equality. change
reduces only local matrix abbreviations and core/Mathlib Matrix.of/function wrappers;
no foreign TCSlib definition is unfolded. The source backward value is accessed solely
through backward_eq and backward_root, and tuple extension solely through extend_eq.
There is no new public definition, sampler, efficiency witness or machine.

The existing Layered imports already expose PathAlgebra, PrefixAlgebra and the precise
ColumnRowPartitioned block APIs. No extra import or new helper search/probe is needed.
Focused source/conclusion and public-lemma searches are in Layered.backward_action.searches.txt.
The body adds roughly seventy lines, retaining substantial margin below the 1000-line cap.

The statement remains total for p=1 and l/n/d=0, without prime, rank, nonzero or positive
size hypotheses. No mathematical obstruction was identified. The earlier explicit
pending-flow warning is superseded by the lead's latest successful native flow check;
the present candidate itself still requires native validation before certification.
