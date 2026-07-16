import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

namespace Schnorr
variable {G : Type*} [CommGroup G]
variable {q : ℕ} [Fact q.Prime]
variable (g : G)
abbrev Transcript (G : Type*) (q : ℕ) := G × ZMod q × ZMod q
end Schnorr

namespace Schnorr
variable {G : Type*} [CommGroup G]
variable {q : ℕ} [Fact q.Prime]
variable (g : G)
def commit (r : ZMod q) : G := g ^ r.val
end Schnorr

namespace Schnorr
variable {G : Type*} [CommGroup G]
variable {q : ℕ} [Fact q.Prime]
variable (g : G)
def respond (w r c : ZMod q) : ZMod q := r + c * w
end Schnorr

namespace Schnorr
variable {G : Type*} [CommGroup G]
variable {q : ℕ} [Fact q.Prime]
variable (g : G)
def Verify (pk a : G) (c s : ZMod q) : Prop :=
  g ^ s.val = a * pk ^ c.val
end Schnorr

namespace Schnorr
variable {G : Type*} [CommGroup G]
variable {q : ℕ} [Fact q.Prime]
variable (g : G)
def honest (w r c : ZMod q) : Transcript G q :=
  (commit g r, c, respond w r c)
end Schnorr

namespace Schnorr
variable {G : Type*} [CommGroup G]
variable {q : ℕ} [Fact q.Prime]
variable (g : G)
def simulate (pk : G) (c s : ZMod q) : Transcript G q :=
  (g ^ s.val * (pk ^ c.val)⁻¹, c, s)
end Schnorr

namespace Schnorr
variable {G : Type*} [CommGroup G]
variable {q : ℕ} [Fact q.Prime]
variable (g : G)
theorem schnorr_completeness
    (hg : orderOf g = q) (w r c : ZMod q) :
    Verify g (g ^ w.val) (commit g r) c (respond w r c) := by
  simp only [Verify, commit, respond]
  rw [← pow_mul, ← pow_add, pow_eq_pow_iff_modEq, hg]
  have h1 : (r + c * w).val ≡ r.val + (c * w).val [MOD q] := by
    rw [ZMod.val_add]
    exact Nat.mod_modEq _ _
  have h2 : (c * w).val ≡ w.val * c.val [MOD q] := by
    rw [ZMod.val_mul, mul_comm]
    exact Nat.mod_modEq _ _
  exact h1.trans (h2.add_left _)
end Schnorr

namespace Schnorr
variable {G : Type*} [CommGroup G]
variable {q : ℕ} [Fact q.Prime]
variable (g : G)
def reindex (w c : ZMod q) : ZMod q ≃ ZMod q where
  toFun r := r + c * w
  invFun s := s - c * w
  left_inv := by intro r; ring
  right_inv := by intro s; ring
end Schnorr

namespace Schnorr
variable {G : Type*} [CommGroup G]
variable {q : ℕ} [Fact q.Prime]
variable (g : G)
theorem schnorr_hvzk
    (hg : orderOf g = q) (w c : ZMod q) :
    (fun r => honest g w r c) =
    (fun r => simulate g (g ^ w.val) c (reindex w c r)) := by
  funext r
  simp only [honest, simulate, commit, respond, reindex]
  refine Prod.ext ?_ rfl
  rw [eq_mul_inv_iff_mul_eq]
  exact (schnorr_completeness g hg w r c).symm
end Schnorr
