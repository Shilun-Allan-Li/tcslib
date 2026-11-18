/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.PartialGarbling.Defs
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Classes
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.BigOperators

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Layered polynomial partial garbling

The instance specializes [AGW20, Appendix A, (28)–(32), pp.37–38] to the
coefficient-tensor representation of a polynomial vector. Its conceptual vertices
are padded public-variable prefixes, output vertices and one sink. No branching-
program datatype is introduced.

The proof route uses forward and backward path sums and a translation of the
random draw. This replaces the source's determinant argument while preserving its
matrix formulas and exact law. It is the one-private-tail-column case of
[IW14, Theorem 3, p.8]. Degree zero and an empty output vector are permitted.

## Main definitions

* `PartialGarbling.Layered.MIdx`, `TIdx`: prefix nodes and non-root prefix nodes.
* `PartialGarbling.Layered.L1`, `L0`: public-variable and constant incidence matrices.
* `PartialGarbling.Layered.rec`: forward path values for reconstruction.
* `PartialGarbling.Layered.backward`, `shift`: backward values for privacy.
* `layeredPG_raw`: the raw uniform family; efficiency is a later target.

## Main results

* `PartialGarbling.Layered.forward_action`, `backward_action`: path-sum identities.
* `PartialGarbling.Layered.translation`: the pointwise real/simulated garbling identity.
* `PartialGarbling.Layered.rec_spec`, `privacy`: reconstruction and exact privacy.
* `layeredPG_raw_*`: readers for every algorithm and its coordinate types.

## References

* [AGW20] M. Abdalla, J. Gong, H. Wee, *Functional Encryption for Attribute-Weighted
  Sums from k-Lin*, 2020, Lemma 2, p.12, Appendix A, pp.37–38, (28)–(32).
* [IW14] Y. Ishai, H. Wee, *Partial Garbling Schemes and Their Applications*, 2014,
  Definition 1, pp.6–7, Theorem 3, p.8, and §4.2, pp.9–11.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption

open Complexity Turing TCSlib.Cryptography.Games

namespace PartialGarbling.Layered

/-- Non-output nodes are all padded public-variable prefixes of lengths 0 through d.
This is the layered specialization of [AGW20, Appendix A, p.37]. -/
abbrev MIdx (l d : ℕ) : Type := Σ k : Fin (d + 1), Fin k.val → Fin (l + 1)

/-- Non-output indices have the displayed prefix-node type. -/
theorem mIdx_eq (l d : ℕ) :
    MIdx l d = (Σ k : Fin (d + 1), Fin k.val → Fin (l + 1)) := rfl

/-- Auxiliary draw nodes are all non-root prefixes, indexed by their predecessor
length. [AGW20, Appendix A, (28)–(32), pp.37–38], layered specialization. -/
abbrev TIdx (l d : ℕ) : Type := Σ k : Fin d, Fin (k.val + 1) → Fin (l + 1)

/-- Auxiliary draw indices have the displayed non-root-prefix type. -/
theorem tIdx_eq (l d : ℕ) :
    TIdx l d = (Σ k : Fin d, Fin (k.val + 1) → Fin (l + 1)) := rfl

/-- The distinguished coordinate is the empty prefix, namely the source node.
[AGW20, Appendix A, (30), p.37]. -/
def root (l d : ℕ) : MIdx l d := ⟨⟨0, Nat.zero_lt_succ d⟩, Fin.elim0⟩

/-- The distinguished coordinate is the explicit depth-zero prefix. -/
theorem root_eq (l d : ℕ) : root l d = ⟨⟨0, Nat.zero_lt_succ d⟩, Fin.elim0⟩ := rfl

/-- An auxiliary prefix is viewed as its corresponding non-output node. -/
def node {l d : ℕ} (v : TIdx l d) : MIdx l d := ⟨v.1.succ, v.2⟩

/-- The auxiliary-node embedding increments its predecessor depth. -/
theorem node_eq {l d : ℕ} (v : TIdx l d) : node v = ⟨v.1.succ, v.2⟩ := rfl

/-- The parent of a non-root prefix deletes its last label. -/
def parent {l d : ℕ} (v : TIdx l d) : MIdx l d := ⟨v.1.castSucc, Fin.init v.2⟩

/-- The parent is the prefix obtained by the published tuple-init operation. -/
theorem parent_eq {l d : ℕ} (v : TIdx l d) :
    parent v = ⟨v.1.castSucc, Fin.init v.2⟩ := rfl

/-- The edge into a non-root prefix is labeled by its final tuple coordinate. -/
def lastLabel {l d : ℕ} (v : TIdx l d) : Fin (l + 1) := v.2 (Fin.last v.1.val)

/-- The final edge label is the prefix's last coordinate. -/
theorem lastLabel_eq {l d : ℕ} (v : TIdx l d) :
    lastLabel v = v.2 (Fin.last v.1.val) := rfl

/-- A full public-variable tuple identifies its depth-d terminal prefix. -/
def leaf {l d : ℕ} (tau : Fin d → Fin (l + 1)) : MIdx l d := ⟨Fin.last d, tau⟩

/-- A leaf has depth d and the supplied tuple. -/
theorem leaf_eq {l d : ℕ} (tau : Fin d → Fin (l + 1)) :
    leaf tau = ⟨Fin.last d, tau⟩ := rfl

/-- The number of non-output nodes is the sum of padded-prefix counts at every
level. This depends only on l,d, not on coefficients. -/
def nodeCount (l d : ℕ) : ℕ := ∑ k : Fin (d + 1), (l + 1) ^ k.val

/-- The non-output node count is the displayed geometric sum. -/
theorem nodeCount_eq (l d : ℕ) : nodeCount l d = ∑ k : Fin (d + 1), (l + 1) ^ k.val :=
  rfl

/-- The number of auxiliary coordinates is the sum of positive-depth prefix counts. -/
def auxCount (l d : ℕ) : ℕ := ∑ k : Fin d, (l + 1) ^ (k.val + 1)

/-- The auxiliary coordinate count is the displayed positive-depth sum. -/
theorem auxCount_eq (l d : ℕ) : auxCount l d = ∑ k : Fin d, (l + 1) ^ (k.val + 1) :=
  rfl

/-- The fixed node bound is the polynomial sum of (l+1)^k for 0≤k≤d.
It is independent of the modulus and function coefficients. [AGW20, Lemma 2,
p.12], specialized to the fixed-degree layered representation. -/
def nodeBound (l : PolyExpr) : ℕ → PolyExpr
  | 0 => .const 1
  | d + 1 => .add (nodeBound l d) (.pow (.add l (PolyExpr.const 1)) (d + 1))

/-- At degree zero the node bound is the constant polynomial 1. -/
theorem nodeBound_zero (l : PolyExpr) : nodeBound l 0 = .const 1 := rfl

/-- Increasing the degree adds the count of the next prefix layer. -/
theorem nodeBound_succ (l : PolyExpr) (d : ℕ) :
    nodeBound l (d + 1) = .add (nodeBound l d) (.pow (.add l (PolyExpr.const 1)) (d + 1)) := rfl

/-- The polynomial node bound equals the exact geometric node count.

**Proof sketch.** Induct on d. The base geometric sum consists only of 1.
At a successor, use Fin.sum_univ_castSucc to split the last layer; its count
is exactly the power added by nodeBound_succ. -/
theorem nodeBound_eval (l : PolyExpr) (d kappa : ℕ) :
    (nodeBound l d).eval kappa = nodeCount (l.eval kappa) d := sorry

/-- Removing the source leaves exactly the auxiliary prefix nodes.

**Proof sketch.** Split the geometric sum at depth zero using Fin.sum_univ_succ;
the first term is 1 and the remaining terms are exactly auxCount. -/
theorem auxCount_add_one (l d : ℕ) : auxCount l d + 1 = nodeCount l d := sorry

/-- Node coordinates use the explicit tuple equivalence within each depth and
the published finite-sigma equivalence between depths. No opaque enumeration is used. -/
def nodeCoord (l d : ℕ) : MIdx l d ≃ Fin (nodeCount l d) :=
  (Equiv.sigmaCongrRight (fun k : Fin (d + 1) => tupleCoord l k.val)).trans finSigmaFinEquiv

/-- Node coordinates are the displayed composition of public equivalences. -/
theorem nodeCoord_eq (l d : ℕ) : nodeCoord l d =
    (Equiv.sigmaCongrRight (fun k : Fin (d + 1) => tupleCoord l k.val)).trans
      finSigmaFinEquiv := rfl

/-- Auxiliary coordinates use explicit positive-depth tuple ranks and finite-sigma ranks. -/
def auxCoord (l d : ℕ) : TIdx l d ≃ Fin (auxCount l d) :=
  (Equiv.sigmaCongrRight (fun k : Fin d => tupleCoord l (k.val + 1))).trans finSigmaFinEquiv

/-- Auxiliary coordinates are the displayed composition of public equivalences. -/
theorem auxCoord_eq (l d : ℕ) : auxCoord l d =
    (Equiv.sigmaCongrRight (fun k : Fin d => tupleCoord l (k.val + 1))).trans
      finSigmaFinEquiv := rfl

/-- The source is finite coordinate zero, fixing the distinguished e1 position.

**Proof sketch.** Apply the published finite-sigma coordinate formula at depth
zero; its prefix sum is empty and its empty tuple has the only coordinate in Fin 1. -/
theorem nodeCoord_root (l d : ℕ) : (nodeCoord l d (root l d)).val = 0 := sorry

section Algorithms

variable {p : ℕ+} {l n d : ℕ}

/-- L1 places the variable-edge coefficients at parent columns and child rows.
Output rows are zero. This is the layered coefficient matrix of
[AGW20, Appendix A, (32), p.38], with the corrected t×(lm) shape. -/
def L1 (C : PolyTensor p l n d) :
    Matrix (TIdx l d ⊕ Fin n) (Fin l × MIdx l d) (ZMod (p : ℕ)) :=
  fun row iu => match row with
    | Sum.inl v => if iu.2 = parent v ∧ lastLabel v = iu.1.castSucc then 1 else 0
    | Sum.inr _ => 0

/-- A non-root L1 row records the variable-labeled edge from its parent. -/
theorem L1_inl (C : PolyTensor p l n d) (v : TIdx l d) (i : Fin l) (u : MIdx l d) :
    L1 C (Sum.inl v) (i, u) =
      if u = parent v ∧ lastLabel v = i.castSucc then 1 else 0 := rfl

/-- Every output row of L1 is zero. -/
theorem L1_inr (C : PolyTensor p l n d) (j : Fin n) (iu : Fin l × MIdx l d) :
    L1 C (Sum.inr j) iu = 0 := rfl

/-- L0 records constant-labeled edges, the negative non-root diagonal, and the
terminal coefficient edges. [AGW20, Appendix A, (32), p.38], layered specialization. -/
def L0 (C : PolyTensor p l n d) :
    Matrix (TIdx l d ⊕ Fin n) (MIdx l d) (ZMod (p : ℕ)) :=
  fun row u => match row with
    | Sum.inl v =>
      (if u = parent v ∧ lastLabel v = Fin.last l then 1 else 0) -
        (if u = node v then 1 else 0)
    | Sum.inr j => ∑ tau : Fin d → Fin (l + 1), if u = leaf tau then C j tau else 0

/-- A non-root L0 row contains its constant edge and negative diagonal. -/
theorem L0_inl (C : PolyTensor p l n d) (v : TIdx l d) (u : MIdx l d) :
    L0 C (Sum.inl v) u =
      (if u = parent v ∧ lastLabel v = Fin.last l then 1 else 0) -
        (if u = node v then 1 else 0) := rfl

/-- An output L0 row contains precisely the corresponding terminal coefficients. -/
theorem L0_inr (C : PolyTensor p l n d) (j : Fin n) (u : MIdx l d) :
    L0 C (Sum.inr j) u =
      ∑ tau : Fin d → Fin (l + 1), if u = leaf tau then C j tau else 0 := rfl

/-- The public-input matrix combines the variable and constant parts as in
[AGW20, Appendix A, (32), p.38]. -/
def matrix (C : PolyTensor p l n d) (x : Fin l → ZMod (p : ℕ)) :
    Matrix (TIdx l d ⊕ Fin n) (MIdx l d) (ZMod (p : ℕ)) :=
  L1 C * PartialGarbling.publicTensor x + L0 C

/-- The input matrix is exactly L1(x⊗I)+L0. -/
theorem matrix_eq (C : PolyTensor p l n d) (x : Fin l → ZMod (p : ℕ)) :
    matrix C x = L1 C * PartialGarbling.publicTensor x + L0 C := rfl

/-- A forward path value is the product of the labels in its prefix. This replaces
the cofactor description of rec in [AGW20, Appendix A, p.38] by its path formula. -/
def forward (x : Fin l → ZMod (p : ℕ)) (u : MIdx l d) : ZMod (p : ℕ) :=
  ∏ i : Fin u.1.val, xhat x (u.2 i)

/-- Forward values are the displayed finite label products. -/
theorem forward_eq (x : Fin l → ZMod (p : ℕ)) (u : MIdx l d) :
    forward x u = ∏ i : Fin u.1.val, xhat x (u.2 i) := rfl

/-- The source's forward value is the empty product 1.

**Proof sketch.** The root tuple has domain Fin 0; its finite product is empty. -/
theorem forward_root (x : Fin l → ZMod (p : ℕ)) : forward x (root l d) = 1 := sorry

/-- Reconstruction consists of the polynomial outputs followed by all forward
prefix values. [AGW20, Lemma 2, p.12; Appendix A, p.38]. -/
def rec (C : PolyTensor p l n d) (x : Fin l → ZMod (p : ℕ)) :
    (Fin n ⊕ MIdx l d) → ZMod (p : ℕ) :=
  Sum.elim (polyTensorEval C x) (forward x)

/-- The output-coordinate reconstruction block is the evaluated polynomial vector. -/
theorem rec_inl (C : PolyTensor p l n d) (x : Fin l → ZMod (p : ℕ)) (j : Fin n) :
    rec C x (Sum.inl j) = polyTensorEval C x j := rfl

/-- The non-output reconstruction block is the forward prefix vector. -/
theorem rec_inr (C : PolyTensor p l n d) (x : Fin l → ZMod (p : ℕ)) (u : MIdx l d) :
    rec C x (Sum.inr u) = forward x u := rfl

/-- Extend a prefix by a suffix to obtain a full degree-d tuple. The length cast
uses the prefix's certified bound and does not choose an enumeration. -/
def extend (u : MIdx l d) (sigma : Fin (d - u.1.val) → Fin (l + 1)) :
    Fin d → Fin (l + 1) :=
  fun i => Fin.append u.2 sigma
    (Fin.cast (Nat.add_sub_of_le (Nat.le_of_lt_succ u.1.isLt)).symm i)

/-- Prefix extension is the displayed tuple append after the canonical length cast. -/
theorem extend_eq (u : MIdx l d) (sigma : Fin (d - u.1.val) → Fin (l + 1)) :
    extend u sigma = fun i => Fin.append u.2 sigma
      (Fin.cast (Nat.add_sub_of_le (Nat.le_of_lt_succ u.1.isLt)).symm i) := rfl

/-- A backward value sums all suffix paths, weighted by terminal coefficients and
private values. This is the path form of the source's privacy translation.
[AGW20, Appendix A, (28)–(30), p.37; IW14, §4.2, p.11]. -/
def backward (C : PolyTensor p l n d) (x : Fin l → ZMod (p : ℕ))
    (z : Fin n → ZMod (p : ℕ)) (u : MIdx l d) : ZMod (p : ℕ) :=
  ∑ sigma : Fin (d - u.1.val) → Fin (l + 1),
    (∑ j : Fin n, C j (extend u sigma) * z j) *
      ∏ i : Fin (d - u.1.val), xhat x (sigma i)

/-- Backward values are the displayed finite suffix sums. -/
theorem backward_eq (C : PolyTensor p l n d) (x : Fin l → ZMod (p : ℕ))
    (z : Fin n → ZMod (p : ℕ)) (u : MIdx l d) :
    backward C x z u =
      ∑ sigma : Fin (d - u.1.val) → Fin (l + 1),
        (∑ j : Fin n, C j (extend u sigma) * z j) *
          ∏ i : Fin (d - u.1.val), xhat x (sigma i) := rfl

/-- The draw translation uses backward values at non-root nodes and the private
values at output nodes. [AGW20, Appendix A, (28)–(30), p.37], path-sum proof route. -/
def shift (C : PolyTensor p l n d) (x : Fin l → ZMod (p : ℕ))
    (z : Fin n → ZMod (p : ℕ)) : (TIdx l d ⊕ Fin n) → ZMod (p : ℕ) :=
  Sum.elim (fun v => backward C x z (node v)) z

/-- The auxiliary draw shift is the corresponding node's backward value. -/
theorem shift_inl (C : PolyTensor p l n d) (x : Fin l → ZMod (p : ℕ))
    (z : Fin n → ZMod (p : ℕ)) (v : TIdx l d) :
    shift C x z (Sum.inl v) = backward C x z (node v) := rfl

/-- The output draw shift equals the original private vector. -/
theorem shift_inr (C : PolyTensor p l n d) (x : Fin l → ZMod (p : ℕ))
    (z : Fin n → ZMod (p : ℕ)) (j : Fin n) : shift C x z (Sum.inr j) = z j := rfl

/-- Applying the input matrix to forward values cancels every internal prefix
row and leaves exactly the polynomial vector on output rows.

**Proof sketch.** Use the variable/constant edge readers and the Fin.snoc product
recurrence. At each non-root prefix its parent's weighted forward value cancels
its own value. Output rows sum the coefficient-weighted full prefix products. -/
theorem forward_action (C : PolyTensor p l n d) (x : Fin l → ZMod (p : ℕ)) :
    Matrix.mulVec (matrix C x) (forward x) =
      Sum.elim (fun _ : TIdx l d => 0) (polyTensorEval C x) := sorry

/-- The backward value at the source is the allowed scalar z·f(x).

**Proof sketch.** At the empty prefix the suffix is the full monomial tuple.
Its extension is itself. Exchange the finite output/tuple sums and regroup the
coefficient products into polyTensorEval. -/
theorem backward_root (C : PolyTensor p l n d) (x : Fin l → ZMod (p : ℕ))
    (z : Fin n → ZMod (p : ℕ)) :
    backward C x z (root l d) = dotProduct z (polyTensorEval C x) := sorry

/-- Multiplying the backward draw shift by the input matrix cancels every column
except the source column, whose value is the allowed scalar.

**Proof sketch.** Split each nonempty suffix into first label and remaining
suffix using Fin.consEquiv, and use Fin.snoc to extend the prefix. Thus each
internal column's weighted child sum equals its backward value and cancels its
negative diagonal. Terminal columns use the coefficient-weighted z values.
The source has no negative diagonal; apply backward_root there. -/
theorem backward_action (C : PolyTensor p l n d) (x : Fin l → ZMod (p : ℕ))
    (z : Fin n → ZMod (p : ℕ)) :
    Matrix.vecMul (shift C x z) (matrix C x) =
      fun u => if u = root l d then dotProduct z (polyTensorEval C x) else 0 := sorry

/-- Every real garbling reconstructs z·f(x), independently of its draw.
[AGW20, Lemma 2, p.12; Appendix A, p.38], proved by path sums.

**Proof sketch.** Split the garbling/reconstruction dot product into its output
and non-output blocks. Move the latter matrix action onto forward values using
the published dot-product/mulVec identity, then apply forward_action. The masked
output contribution cancels the draw contribution, leaving z·f(x). -/
theorem rec_spec (C : PolyTensor p l n d) (x : Fin l → ZMod (p : ℕ))
    (z : Fin n → ZMod (p : ℕ)) (t : (TIdx l d ⊕ Fin n) → ZMod (p : ℕ)) :
    dotProduct (PartialGarbling.pgbCore (L1 C) (L0 C) x z t) (rec C x) =
      dotProduct z (polyTensorEval C x) := sorry

/-- Subtracting the backward draw shift transforms the real garbling exactly
into the simulated garbling at its allowed scalar. [AGW20, Appendix A, (28)–(30),
p.37; IW14, §4.2, p.11], with path sums replacing the determinant argument.

**Proof sketch.** At output coordinates, −(t−z)=z−t. At non-output coordinates,
linearity of vecMul and backward_action give (t−s)B+μe_source=tB. This proves the
pointwise identity with the subtraction sign shown, including empty index types. -/
theorem translation (C : PolyTensor p l n d) (x : Fin l → ZMod (p : ℕ))
    (z : Fin n → ZMod (p : ℕ)) (t : (TIdx l d ⊕ Fin n) → ZMod (p : ℕ)) :
    PartialGarbling.pgbCore (L1 C) (L0 C) x z t =
      PartialGarbling.pgbStarCore (L1 C) (L0 C) (root l d) x
        (dotProduct z (polyTensorEval C x)) (t - shift C x z) := sorry

/-- Real and simulated layered garblings have identical laws, with no error term.
[IW14, Definition 1, p.6; AGW20, Appendix A, (28)–(30), p.37].

**Proof sketch.** Apply the pointwise translation, then reindex the uniform draw
by Equiv.addRight (−shift C x z), using ProbComp.expect_sample_equiv. No rank,
nonzero-value or positive-dimension event is needed. -/
theorem privacy (C : PolyTensor p l n d) (x : Fin l → ZMod (p : ℕ))
    (z : Fin n → ZMod (p : ℕ)) (test : ((Fin n ⊕ MIdx l d) → ZMod (p : ℕ)) → ℝ) :
    ProbComp.expect (ProbComp.sample ((TIdx l d ⊕ Fin n) → ZMod (p : ℕ)))
        (fun t => test (PartialGarbling.pgbCore (L1 C) (L0 C) x z t)) =
      ProbComp.expect (ProbComp.sample ((TIdx l d ⊕ Fin n) → ZMod (p : ℕ)))
        (fun t => test (PartialGarbling.pgbStarCore (L1 C) (L0 C) (root l d)
          x (dotProduct z (polyTensorEval C x)) t)) := sorry

end Algorithms
end PartialGarbling.Layered

/-- The layered raw family instantiates the corrected partial-garbling interface
for padded polynomial tensors. [AGW20, Appendix A, (28)–(32), pp.37–38; IW14,
Theorem 3, p.8], specialized to one private-tail column.

The algorithms and index coordinates are explicit. Correctness and exact privacy
use forward/backward path sums and translation, rather than determinants. The
family covers every positive modulus; no efficiency proof is assumed or constructed. -/
def layeredPG_raw (l n : PolyExpr) (d : ℕ) :
    PartialGarbling.Raw l n (fun kappa p => PolyTensor p (l.eval kappa) (n.eval kappa) d) where
  MIdx := fun kappa _ _ => PartialGarbling.Layered.MIdx (l.eval kappa) d
  TIdx := fun kappa _ _ => PartialGarbling.Layered.TIdx (l.eval kappa) d
  mFinite := fun _ _ _ => inferInstance
  tFinite := fun _ _ _ => inferInstance
  mDecEq := fun _ _ _ => inferInstance
  tDecEq := fun _ _ _ => inferInstance
  mCount := fun kappa _ _ => PartialGarbling.Layered.nodeCount (l.eval kappa) d
  mBound := PartialGarbling.Layered.nodeBound l d
  mCount_le_mBound := fun kappa _ _ =>
    (PartialGarbling.Layered.nodeBound_eval l d kappa).ge
  auxCount := fun kappa _ _ => PartialGarbling.Layered.auxCount (l.eval kappa) d
  mCoord := fun kappa _ _ => PartialGarbling.Layered.nodeCoord (l.eval kappa) d
  tCoord := fun kappa _ _ => PartialGarbling.Layered.auxCoord (l.eval kappa) d
  auxCount_add_one := fun kappa _ _ =>
    PartialGarbling.Layered.auxCount_add_one (l.eval kappa) d
  m0 := fun kappa _ _ => PartialGarbling.Layered.root (l.eval kappa) d
  m0_coord := fun kappa _ _ => PartialGarbling.Layered.nodeCoord_root (l.eval kappa) d
  fnLen := fun kappa p => n.eval kappa * (l.eval kappa + 1) ^ d * Nat.size (p : ℕ)
  encFn := fun _ p C => encodeTensorBits (Nat.size (p : ℕ)) C
  encFn_inj := fun _ p => encodeTensorBits_injective (Nat.size (p : ℕ))
    (Nat.le_of_lt (Nat.lt_size_self (p : ℕ)))
  eval := fun _ _ C => polyTensorEval C
  L1 := fun _ _ C => PartialGarbling.Layered.L1 C
  L0 := fun _ _ C => PartialGarbling.Layered.L0 C
  recVec := fun _ _ C => PartialGarbling.Layered.rec C
  rec_spec := fun _ _ C => PartialGarbling.Layered.rec_spec C
  privacy := fun _ _ C => PartialGarbling.Layered.privacy C

/-- The layered raw family's non-output coordinates are exactly its prefix nodes. -/
theorem layeredPG_raw_MIdx (l n : PolyExpr) (d kappa : ℕ) (p : ℕ+)
    (C : PolyTensor p (l.eval kappa) (n.eval kappa) d) :
    (layeredPG_raw l n d).MIdx kappa p C =
      PartialGarbling.Layered.MIdx (l.eval kappa) d := rfl

/-- The layered raw family's auxiliary coordinates are exactly its non-root prefixes. -/
theorem layeredPG_raw_TIdx (l n : PolyExpr) (d kappa : ℕ) (p : ℕ+)
    (C : PolyTensor p (l.eval kappa) (n.eval kappa) d) :
    (layeredPG_raw l n d).TIdx kappa p C =
      PartialGarbling.Layered.TIdx (l.eval kappa) d := rfl

/-- The layered non-output dimension is independent of the coefficient tensor. -/
theorem layeredPG_raw_mCount (l n : PolyExpr) (d kappa : ℕ) (p : ℕ+)
    (C : PolyTensor p (l.eval kappa) (n.eval kappa) d) :
    (layeredPG_raw l n d).mCount kappa p C =
      PartialGarbling.Layered.nodeCount (l.eval kappa) d := rfl

/-- The raw family's fixed bound is the polynomial sum of its layer counts. -/
theorem layeredPG_raw_mBound (l n : PolyExpr) (d : ℕ) :
    (layeredPG_raw l n d).mBound = PartialGarbling.Layered.nodeBound l d := rfl

/-- The bound evaluates to the exact node count, so padded reductions lose no
extra statistical term from the layered instance's dimension bound. -/
theorem layeredPG_raw_mBound_eval (l n : PolyExpr) (d kappa : ℕ) :
    (layeredPG_raw l n d).mBound.eval kappa =
      PartialGarbling.Layered.nodeCount (l.eval kappa) d :=
  PartialGarbling.Layered.nodeBound_eval l d kappa

/-- The layered auxiliary dimension is independent of the coefficient tensor. -/
theorem layeredPG_raw_auxCount (l n : PolyExpr) (d kappa : ℕ) (p : ℕ+)
    (C : PolyTensor p (l.eval kappa) (n.eval kappa) d) :
    (layeredPG_raw l n d).auxCount kappa p C =
      PartialGarbling.Layered.auxCount (l.eval kappa) d := rfl

/-- The raw matrix-generation algorithms are the explicit layered matrices L1. -/
theorem layeredPG_raw_L1 (l n : PolyExpr) (d kappa : ℕ) (p : ℕ+)
    (C : PolyTensor p (l.eval kappa) (n.eval kappa) d) :
    (layeredPG_raw l n d).L1 kappa p C = PartialGarbling.Layered.L1 C := rfl

/-- The raw constant matrices are the explicit layered matrices L0. -/
theorem layeredPG_raw_L0 (l n : PolyExpr) (d kappa : ℕ) (p : ℕ+)
    (C : PolyTensor p (l.eval kappa) (n.eval kappa) d) :
    (layeredPG_raw l n d).L0 kappa p C = PartialGarbling.Layered.L0 C := rfl

/-- The raw reconstruction algorithm is the explicit forward path vector. -/
theorem layeredPG_raw_rec (l n : PolyExpr) (d kappa : ℕ) (p : ℕ+)
    (C : PolyTensor p (l.eval kappa) (n.eval kappa) d) :
    (layeredPG_raw l n d).recVec kappa p C = PartialGarbling.Layered.rec C := rfl

/-- The raw evaluated vector is the shared coefficient-tensor evaluation. -/
theorem layeredPG_raw_eval (l n : PolyExpr) (d kappa : ℕ) (p : ℕ+)
    (C : PolyTensor p (l.eval kappa) (n.eval kappa) d) :
    (layeredPG_raw l n d).eval kappa p C = polyTensorEval C := rfl

/-- The raw function-description width follows the input modulus, permitting one
uniform efficient interface for every positive modulus. -/
theorem layeredPG_raw_fnLen (l n : PolyExpr) (d kappa : ℕ) (p : ℕ+) :
    (layeredPG_raw l n d).fnLen kappa p =
      n.eval kappa * (l.eval kappa + 1) ^ d * Nat.size (p : ℕ) := rfl

/-- The raw function encoding is the shared canonical tensor encoding. -/
theorem layeredPG_raw_encFn (l n : PolyExpr) (d kappa : ℕ) (p : ℕ+)
    (C : PolyTensor p (l.eval kappa) (n.eval kappa) d) :
    (layeredPG_raw l n d).encFn kappa p C = encodeTensorBits (Nat.size (p : ℕ)) C := rfl

/-- The raw distinguished coordinate is the empty prefix. -/
theorem layeredPG_raw_m0 (l n : PolyExpr) (d kappa : ℕ) (p : ℕ+)
    (C : PolyTensor p (l.eval kappa) (n.eval kappa) d) :
    (layeredPG_raw l n d).m0 kappa p C = PartialGarbling.Layered.root (l.eval kappa) d := rfl

/-- The raw non-output coordinate encoding uses explicit tuple and depth ranks. -/
theorem layeredPG_raw_mCoord (l n : PolyExpr) (d kappa : ℕ) (p : ℕ+)
    (C : PolyTensor p (l.eval kappa) (n.eval kappa) d) :
    (layeredPG_raw l n d).mCoord kappa p C =
      PartialGarbling.Layered.nodeCoord (l.eval kappa) d := rfl

/-- The raw auxiliary coordinate encoding uses explicit positive-depth tuple ranks. -/
theorem layeredPG_raw_tCoord (l n : PolyExpr) (d kappa : ℕ) (p : ℕ+)
    (C : PolyTensor p (l.eval kappa) (n.eval kappa) d) :
    (layeredPG_raw l n d).tCoord kappa p C =
      PartialGarbling.Layered.auxCoord (l.eval kappa) d := rfl

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption
