import Mathlib

open Finset Complex

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace ZkFourier
def ZkVec (k n : ℕ) := Fin n → ZMod k
end ZkFourier

namespace ZkFourier
instance {k n : ℕ} : DecidableEq (ZkVec k n) := by
  unfold ZkVec; infer_instance
end ZkFourier

namespace ZkFourier
instance {k n : ℕ} [NeZero k] : Fintype (ZkVec k n) := by
  unfold ZkVec; infer_instance
end ZkFourier

namespace ZkFourier
instance {k n : ℕ} : AddCommGroup (ZkVec k n) := Pi.addCommGroup
end ZkFourier

namespace ZkFourier
instance {k n : ℕ} : Module (ZMod k) (ZkVec k n) := Pi.module _ _ _
end ZkFourier

namespace ZkFourier
noncomputable def rootOfUnity (k : ℕ) : ℂ :=
  Complex.exp (2 * ↑Real.pi * I / (k : ℂ))
end ZkFourier

namespace ZkFourier
noncomputable def toOmega {k : ℕ} [NeZero k] (a : ZMod k) : ℂ :=
  rootOfUnity k ^ a.val
end ZkFourier

namespace ZkFourier
@[simp]
lemma toOmega_zero {k : ℕ} [NeZero k] : toOmega (0 : ZMod k) = 1 := by
  simp [toOmega, ZMod.val_zero]
end ZkFourier

namespace ZkFourier
lemma norm_toOmega {k : ℕ} [NeZero k] (a : ZMod k) :
    ‖toOmega a‖ = 1 := by
      unfold toOmega;
      unfold rootOfUnity; norm_num [ Complex.norm_exp ] ;
end ZkFourier

namespace ZkFourier
def ZkFun (k n : ℕ) := ZkVec k n → ℂ
end ZkFourier

namespace ZkFourier
variable {k : ℕ} [NeZero k] {n : ℕ}
def zkDot (s x : ZkVec k n) : ZMod k := ∑ i : Fin n, s i * x i
end ZkFourier

namespace ZkFourier
variable {k : ℕ} [NeZero k] {n : ℕ}
noncomputable def char_s (s : ZkVec k n) : ZkFun k n :=
  fun x => toOmega (zkDot s x)
end ZkFourier

namespace ZkFourier
variable {k : ℕ} [NeZero k] {n : ℕ}
lemma zkDot_zero_left (x : ZkVec k n) : zkDot 0 x = 0 := by
  exact Finset.sum_eq_zero fun i _ => MulZeroClass.zero_mul _
end ZkFourier

namespace ZkFourier
variable {k : ℕ} [NeZero k] {n : ℕ}
lemma zkDot_zero_right (s : ZkVec k n) : zkDot s 0 = 0 := by
  exact Finset.sum_eq_zero fun _ _ => mul_zero _
end ZkFourier

namespace ZkFourier
variable {k : ℕ} [NeZero k] {n : ℕ}
@[simp]
lemma char_s_zero_vec (s : ZkVec k n) : char_s s 0 = 1 := by
  simp only [char_s, zkDot_zero_right, toOmega_zero]
end ZkFourier

namespace ZkFourier
variable {k : ℕ} [NeZero k] {n : ℕ}
@[simp]
lemma char_s_zero_index (x : ZkVec k n) :
    char_s (0 : ZkVec k n) x = 1 := by
  simp only [char_s, zkDot_zero_left, toOmega_zero]
end ZkFourier
