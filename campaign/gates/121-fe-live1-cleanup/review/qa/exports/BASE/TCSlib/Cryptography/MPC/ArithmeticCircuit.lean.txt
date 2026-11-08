/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Arithmetic circuits over a commutative ring

The function class that secure computation protocols are stated for: expressions built from
inputs and public constants by addition, multiplication, and multiplication by a public constant.
Circuits are represented as trees (so a shared subexpression is duplicated); this is the right
level of detail for correctness of a gate-by-gate protocol, which processes each gate
independently, and it keeps the induction principle free.

## Main definitions

* `TCSlib.MPC.Circuit F ι`: the syntax.
* `TCSlib.MPC.Circuit.eval`: the function a circuit computes.

## References

* [BGW88] M. Ben-Or, S. Goldwasser, A. Wigderson, *Completeness theorems for non-cryptographic
  fault-tolerant distributed computation*, STOC 1988, §1.
* [AL17] G. Asharov, Y. Lindell, *A full proof of the BGW protocol for perfectly secure
  multiparty computation*, J. Cryptology 30(1), 2017, §2.
-/

namespace TCSlib.MPC

universe u v

/-- An arithmetic circuit over `F` with inputs indexed by `ι`, as a tree of gates. [BGW88, §1] -/
inductive Circuit (F : Type u) (ι : Type v) : Type (max u v)
  /-- An input wire. -/
  | input : ι → Circuit F ι
  /-- A public constant. -/
  | const : F → Circuit F ι
  /-- An addition gate. -/
  | add : Circuit F ι → Circuit F ι → Circuit F ι
  /-- Multiplication by a public constant. -/
  | smul : F → Circuit F ι → Circuit F ι
  /-- A multiplication gate. -/
  | mul : Circuit F ι → Circuit F ι → Circuit F ι
  deriving Inhabited

namespace Circuit

variable {F ι : Type*} [CommRing F]

/-- The value a circuit computes on an input assignment. -/
def eval (v : ι → F) : Circuit F ι → F
  | .input i => v i
  | .const c => c
  | .add a b => a.eval v + b.eval v
  | .smul c a => c * a.eval v
  | .mul a b => a.eval v * b.eval v

@[simp] theorem eval_input (v : ι → F) (i : ι) : (input i : Circuit F ι).eval v = v i := rfl
@[simp] theorem eval_const (v : ι → F) (c : F) : (const c : Circuit F ι).eval v = c := rfl
@[simp] theorem eval_add (v : ι → F) (a b : Circuit F ι) :
    (a.add b).eval v = a.eval v + b.eval v := rfl
@[simp] theorem eval_smul (v : ι → F) (c : F) (a : Circuit F ι) :
    (a.smul c).eval v = c * a.eval v := rfl
@[simp] theorem eval_mul (v : ι → F) (a b : Circuit F ι) :
    (a.mul b).eval v = a.eval v * b.eval v := rfl

/-- A circuit is *linear* when it has no multiplication gates: its value is an affine function of
the inputs, and (as `TCSlib.MPC.BGW` shows) it can be evaluated on shares without any
interaction. -/
def IsLinear : Circuit F ι → Prop
  | .input _ => True
  | .const _ => True
  | .add a b => a.IsLinear ∧ b.IsLinear
  | .smul _ a => a.IsLinear
  | .mul _ _ => False

end Circuit

end TCSlib.MPC
