-- Root-only probes; no named proposed helper is imported.
-- Replace one placeholder at a time with exact?, then apply?, in the approved route.
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Lean.Elab.Tactic.LibrarySearch

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption
namespace PartialGarbling.PathAlgebra

-- Search target: weightedIncidence_mulVec
example {V E R : Type*} [Fintype V] [DecidableEq V]
    [Ring R] (parent child : E → V) (weight : E → R) (values : V → R) :
    Matrix.mulVec
      (Matrix.of fun e v =>
        (if v = parent e then weight e else 0) -
          (if v = child e then 1 else 0)) values =
      fun e => weight e * values (parent e) - values (child e) := sorry

-- Search target: weightedIncidence_vecMul
example {V E R : Type*} [Fintype E] [DecidableEq V]
    [Ring R] (parent child : E → V) (weight flow : E → R) :
    Matrix.vecMul flow
      (Matrix.of fun e v =>
        (if v = parent e then weight e else 0) -
          (if v = child e then 1 else 0)) =
      fun v =>
        (∑ e, if parent e = v then flow e * weight e else 0) -
          ∑ e, if child e = v then flow e else 0 := sorry

-- Search target: paddedIncidence_eq
example {V E R : Type*} [Fintype V] [DecidableEq V]
    [Ring R] {l : ℕ} (parent child : E → V) (label : E → Fin (l + 1))
    (x : Fin l → R) :
    (Matrix.of (fun e (iu : Fin l × V) =>
        if iu.2 = parent e ∧ label e = iu.1.castSucc then (1 : R) else 0) :
          Matrix E (Fin l × V) R) *
      (Matrix.of (fun (iu : Fin l × V) v =>
        x iu.1 * (if iu.2 = v then 1 else 0)) : Matrix (Fin l × V) V R) +
      Matrix.of (fun e v =>
        (if v = parent e ∧ label e = Fin.last l then 1 else 0) -
          (if v = child e then 1 else 0)) =
      Matrix.of (fun e v =>
        (if v = parent e then Fin.snoc x 1 (label e) else 0) -
          (if v = child e then 1 else 0)) := sorry

end PartialGarbling.PathAlgebra
end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption
