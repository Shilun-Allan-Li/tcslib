# Exactly one next Layered step: backward_root

Candidate: Layered.backward_root.proof.lean.inc. Existing source/header/docstring are
preserved, with only the admitted proof body replaced. No live edit, Lean/lake/build,
proof-check or Git command was run. One existing admission is drafted; no other theorem,
helper, import, axiom, algorithm or interface is added. ZERO tactic blocks.

## Why this target

The actual Layered module has no forward_node, forward_output or rec_root admission.
Its rec_inl/rec_inr readers are already rfl. backward_root is the simplest remaining
source-value reconstruction step: the source's backward path value must equal the allowed
scalar z·f(x). It is independent of forward_action/backward_action/rec_spec/translation
and does not use any other admitted theorem, even the preceding forward_root candidate.

## Proof route

- u0 is the explicit depth-zero node from root_eq.
- hExtend proves extension from that empty prefix is the original full tuple. It applies
  extend_eq, Fin.elim0_append, Fin.cast_cast and Fin.cast_refl. No generic append/cast
  identity is re-proved inline and no Fin.ext arithmetic argument is invented.
- hWeight reorders one coefficient/private/monomial product by published mul_comm and
  mul_assoc.
- hSum uses published Finset.sum_mul, Finset.sum_comm and Finset.mul_sum to exchange the
  full-tuple/output sums and factor z_j. polyTensorEval_eq identifies each inner sum.
- root_eq/backward_eq and hExtend reduce the source value to hSum. Mathlib dotProduct is
  normalized only in an explicit show/from rfl; no definition is passed to simp/rw/unfold.

The body has45 total fragment lines/max96. This is a substantive but direct path-sum law;
all finite-sum and cast operations are supplied by published APIs. No mathematical
obstruction was found, including d=0,n=0,l=0 and positive modulus1. The prefix cast uses
0+d=d and ordinary proof irrelevance; the existing Nat.sub_zero is definitionally rfl.

The principal unrun elaboration risk is dependent normalization of `extend u0 sigma` from
Fin(d−0) to Fin d, and matching the canonical cast proof with hCast. Actual parent Lean,
Rule10 and axioms checks remain pending; no passing proof is claimed here.

## Search/reuse record

Read exact Layered.lean:257–354: extend/extend_eq, backward/backward_eq, forward_action,
backward_root and following reconstruction statements. Read Classes.polyTensorEval_eq.
Name/conclusion search for backward_root, extend(root...) identity, backward source dot
product across TCSlib/Mathlib/core found only this target and its use in backward_action.

Nearest APIs read directly:

- Fin/Tuple/Basic.lean:328 Fin.elim0_append, exact empty-prefix append formula.
- Core Init/Data/Fin/Lemmas.lean:494 Fin.cast_refl and :497 Fin.cast_cast.
  The deprecated cast_trans alias is deliberately NOT used.
- Core Init/Data/Nat/Basic.lean:264 Nat.sub_zero, body rfl.
- BigOperators/Ring/Finset.lean:49 Finset.sum_mul, :52 Finset.mul_sum.
- BigOperators/Group/Finset/Sigma.lean:117 prod_comm's to_additive theorem Finset.sum_comm;
  implicit arguments are s,t,f, exactly as supplied in hSum.
- Classes.lean:93 polyTensorEval_eq, not the definition body.

Existing Layered imports already include Group.Finset.Sigma and Classes' finite tuple/
BigOperators dependencies. No Mathlib root/import is added.

Root-only overlap probes (NOT EXECUTED):

Existing target:
  {p:ℕ+} {l n d:ℕ} (C:PolyTensor p l n d) (x:Fin l→ZMod(p:ℕ))
    (z:Fin n→ZMod(p:ℕ)) : backward C x z (root l d)=dotProduct z (polyTensorEval C x)

Local hExtend shape, nearest Fin.elim0_append plus cast composition:
  (sigma:Fin d→Fin(l+1)) :
    extend (⟨⟨0,Nat.zero_lt_succ d⟩,Fin.elim0⟩ : MIdx l d) sigma=sigma

Parent should run exact?/apply? as required. No new public helper or frozen-header repair
is needed. If a proof-sketch-only refresh is useful, name the existing conceptual steps
hExtend (empty prefix), hWeight (coefficient regrouping), hSum (finite-sum exchange).
