/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.TrapdoorFunctions.AllButOne.AntiCyclic
import TCSlib.Cryptography.TrapdoorFunctions.Lossy.Matrix

import Mathlib.Tactic.Simps.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The all-but-one concealed-gadget mathematics

## Main definitions

* `branchGadget`: multiply the binary gadget by a branch's anti-cyclic matrix.
* `allButOneKey`: conceal the negative gadget of one designated lossy branch.
* `evaluateBranch`: restore the queried branch's encoded gadget before evaluation.

## Main results

The designated branch cancels exactly to the lossy concealed map and inherits its
quantitative image bound. The other-branch residual and injectivity obligations
use strict bounded-noise separation and the larger message modulus.

## References

* [PW10] C. Peikert, B. Waters, *Lossy Trapdoor Functions and Their Applications*,
  author version 4 June 2010, Section 6.4, printed pages 37--38.

This is a dyadic, bounded-noise mathematical adaptation, with branch width `2^u`,
input length `2^u*b`, message modulus `2^(b+u+1)`, and larger modulus
`2^(b+u+1+a)`. The message modulus prevents signed branch products from aliasing.
Integer injectivity is used after bounded lifting, never invertibility modulo `q`.
No branch-inversion algorithm, concealer security, strong one-time signature,
CCA2 game or efficient primitive bridge is asserted by this module.
-/

namespace TCSlib.Cryptography.TrapdoorFunctions.AllButOne

open Lossy

/-- Multiply the binary block gadget by the branch's integer anti-cyclic matrix
[PW10, Section 6.4, transposed convention]. -/
def branchGadget (b u : ℕ) (v : Fin (2 ^ u) → Bool) :
    Matrix (Fin (2 ^ u * b)) (Fin (2 ^ u)) ℤ :=
  gadget b (2 ^ u) * antiCyclic (fun j => ((v j).toNat : ℤ))

/-- The complete branch gadget is exactly the product of those two integer matrices. -/
theorem branchGadget_eq (b u : ℕ) (v : Fin (2 ^ u) → Bool) :
    branchGadget b u v = gadget b (2 ^ u) * antiCyclic (fun j => ((v j).toNat : ℤ)) := rfl

/-- Conceal the negative encoded gadget of the selected lossy branch
[PW10, Section 6.4, exact dyadic adaptation]. -/
@[simps! (config := { isSimp := false }) fst snd]
def allButOneKey (b a u d : ℕ)
    (A : Matrix (Fin (2 ^ u * b)) (Fin d) (ZMod (2 ^ (b + u + 1 + a))))
    (T : Matrix (Fin (2 ^ u)) (Fin d) (ZMod (2 ^ (b + u + 1 + a))))
    (E : Matrix (Fin (2 ^ u * b)) (Fin (2 ^ u)) ℤ) (vstar : Fin (2 ^ u) → Bool) :
    Matrix (Fin (2 ^ u * b)) (Fin d) (ZMod (2 ^ (b + u + 1 + a))) ×
      Matrix (Fin (2 ^ u * b)) (Fin (2 ^ u)) (ZMod (2 ^ (b + u + 1 + a))) :=
  (A, conceal A T E - Matrix.of (fun i j =>
    encode (b + u + 1) a (branchGadget b u vstar i j : ZMod (2 ^ (b + u + 1)))))

/-- The complete key is the concealed block minus the designated branch's encoded gadget. -/
theorem allButOneKey_eq (b a u d : ℕ)
    (A : Matrix (Fin (2 ^ u * b)) (Fin d) (ZMod (2 ^ (b + u + 1 + a))))
    (T : Matrix (Fin (2 ^ u)) (Fin d) (ZMod (2 ^ (b + u + 1 + a))))
    (E : Matrix (Fin (2 ^ u * b)) (Fin (2 ^ u)) ℤ) (vstar : Fin (2 ^ u) → Bool) :
    allButOneKey b a u d A T E vstar =
      (A, conceal A T E - Matrix.of (fun i j =>
        encode (b + u + 1) a (branchGadget b u vstar i j : ZMod (2 ^ (b + u + 1))))) := rfl

/-- Restore the queried branch's encoded gadget and evaluate the two public blocks
[PW10, Section 6.4, transposed convention]. -/
@[simps! (config := { isSimp := false }) fst snd]
def evaluateBranch (b a u d : ℕ)
    (pk : Matrix (Fin (2 ^ u * b)) (Fin d) (ZMod (2 ^ (b + u + 1 + a))) ×
      Matrix (Fin (2 ^ u * b)) (Fin (2 ^ u)) (ZMod (2 ^ (b + u + 1 + a))))
    (v : Fin (2 ^ u) → Bool) (x : Fin (2 ^ u * b) → Bool) :
    (Fin d → ZMod (2 ^ (b + u + 1 + a))) ×
      (Fin (2 ^ u) → ZMod (2 ^ (b + u + 1 + a))) :=
  evaluate (pk.1, pk.2 + Matrix.of (fun i j =>
    encode (b + u + 1) a (branchGadget b u v i j : ZMod (2 ^ (b + u + 1))))) x

/-- The complete branch evaluator adds precisely the queried branch's encoded matrix. -/
theorem evaluateBranch_eq (b a u d : ℕ)
    (pk : Matrix (Fin (2 ^ u * b)) (Fin d) (ZMod (2 ^ (b + u + 1 + a))) ×
      Matrix (Fin (2 ^ u * b)) (Fin (2 ^ u)) (ZMod (2 ^ (b + u + 1 + a))))
    (v : Fin (2 ^ u) → Bool) (x : Fin (2 ^ u * b) → Bool) :
    evaluateBranch b a u d pk v x =
      evaluate (pk.1, pk.2 + Matrix.of (fun i j =>
        encode (b + u + 1) a (branchGadget b u v i j : ZMod (2 ^ (b + u + 1))))) x := rfl

/-- At the designated branch the two gadget contributions cancel exactly.

**Proof sketch.** Read the key and evaluator equations. In every matrix entry the
negative designated gadget and the same positive gadget cancel, retaining the actual
concealed matrix and its original integer errors. -/
theorem evaluate_lossy_branch (b a u d : ℕ)
    (A : Matrix (Fin (2 ^ u * b)) (Fin d) (ZMod (2 ^ (b + u + 1 + a))))
    (T : Matrix (Fin (2 ^ u)) (Fin d) (ZMod (2 ^ (b + u + 1 + a))))
    (E : Matrix (Fin (2 ^ u * b)) (Fin (2 ^ u)) ℤ) (vstar : Fin (2 ^ u) → Bool)
    (x : Fin (2 ^ u * b) → Bool) :
    evaluateBranch b a u d (allButOneKey b a u d A T E vstar) vstar x =
      evaluate (A, conceal A T E) x := by
  rw [evaluateBranch_eq, allButOneKey_eq]
  simp only [sub_add_cancel]

/-- Cancellation leaves the encoded integer branch-difference product plus the
original error subset sum [PW10, Section 6.4, exact dyadic adaptation].

**Proof sketch.** Cancel the secret product as in the lossy construction. Distribute
the exact additive encoding over both branch matrices, use `antiCyclic_sub`, then
read `gadget_mulVec`. Transposition puts the branch-difference matrix on the digit vector. -/
theorem residual_branch (b a u d : ℕ)
    (A : Matrix (Fin (2 ^ u * b)) (Fin d) (ZMod (2 ^ (b + u + 1 + a))))
    (T : Matrix (Fin (2 ^ u)) (Fin d) (ZMod (2 ^ (b + u + 1 + a))))
    (E : Matrix (Fin (2 ^ u * b)) (Fin (2 ^ u)) ℤ)
    (vstar v : Fin (2 ^ u) → Bool) (x : Fin (2 ^ u * b) → Bool) (j : Fin (2 ^ u)) :
    residual T (evaluateBranch b a u d (allButOneKey b a u d A T E vstar) v x) j =
      encode (b + u + 1) a
        (((antiCyclic (fun i => ((v i).toNat : ℤ) - ((vstar i).toNat : ℤ))).transpose.mulVec
          (fun i => ((digits b (2 ^ u) x i : ℕ) : ℤ)) j : ℤ) : ZMod (2 ^ (b + u + 1))) +
        ((∑ i, E i j * ((x i).toNat : ℤ) : ℤ) : ZMod (2 ^ (b + u + 1 + a))) := by
  sorry

/-- Every other branch defines an injective map for every bounded-error key under
strict rounding separation [PW10, Section 6.4, deterministic dyadic adaptation].

**Proof sketch.** Cancel and round each residual using `residual_branch` and the
bounded error sum. The branch-message bound is strictly below half `2^(b+u+1)`,
so equal decoded residues lift to equal integer messages. Apply the integer
branch-difference injectivity theorem and then digit injectivity. The proof never
inverts a possibly singular matrix modulo the large modulus. -/
theorem evaluateBranch_injective (b a u d : ℕ) (ha : 0 < a)
    (A : Matrix (Fin (2 ^ u * b)) (Fin d) (ZMod (2 ^ (b + u + 1 + a))))
    (T : Matrix (Fin (2 ^ u)) (Fin d) (ZMod (2 ^ (b + u + 1 + a))))
    (E : Matrix (Fin (2 ^ u * b)) (Fin (2 ^ u)) ℤ)
    (vstar v : Fin (2 ^ u) → Bool) (hv : v ≠ vstar) (B : ℕ)
    (hE : ∀ i j, (E i j).natAbs ≤ B) (hsep : 2 * (2 ^ u * b * B) < 2 ^ a) :
    Function.Injective (evaluateBranch b a u d (allButOneKey b a u d A T E vstar) v) := by
  sorry

/-- The designated branch inherits the concealed map's explicit small-image bound.

**Proof sketch.** Apply exact designated-branch cancellation pointwise, then use
`Lossy.lossy_range_card` with the same entrywise integer error bound. -/
theorem lossy_branch_range_card (b a u d : ℕ)
    (A : Matrix (Fin (2 ^ u * b)) (Fin d) (ZMod (2 ^ (b + u + 1 + a))))
    (T : Matrix (Fin (2 ^ u)) (Fin d) (ZMod (2 ^ (b + u + 1 + a))))
    (E : Matrix (Fin (2 ^ u * b)) (Fin (2 ^ u)) ℤ) (vstar : Fin (2 ^ u) → Bool)
    (B : ℕ) (hE : ∀ i j, (E i j).natAbs ≤ B) :
    (Finset.univ.image
      (evaluateBranch b a u d (allButOneKey b a u d A T E vstar) vstar)).card ≤
      (2 ^ (b + u + 1 + a)) ^ d * (2 * (2 ^ u * b) * B + 1) ^ (2 ^ u) := by
  have h : evaluateBranch b a u d (allButOneKey b a u d A T E vstar) vstar =
      evaluate (A, conceal A T E) :=
    funext (evaluate_lossy_branch b a u d A T E vstar)
  rw [h]
  exact lossy_range_card A T E B hE

end TCSlib.Cryptography.TrapdoorFunctions.AllButOne
