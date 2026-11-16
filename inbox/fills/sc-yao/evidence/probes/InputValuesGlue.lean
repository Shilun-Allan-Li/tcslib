import TCSlib.Cryptography.SecureComputation.Yao

namespace TCSlib.Cryptography.SecureComputation
open Complexity Turing BoolCircuit

example {m n : ℕ} (C : DAGCircuit (m + n)) (x : Fin m → Bool) (y : Fin n → Bool) :
    (∀ i : Fin m, (C.values (Fin.append x y)).getD i false = x i) ∧
      ∀ j : Fin n, (C.values (Fin.append x y)).getD (m + j) false = y j := by
  constructor
  · intro i
    simpa only [Fin.coe_castAdd, Fin.append_left] using
      C.values_getD_input (Fin.append x y) (Fin.castAdd n i)
  · intro j
    simpa only [Fin.coe_natAdd, Fin.append_right] using
      C.values_getD_input (Fin.append x y) (Fin.natAdd m j)

end TCSlib.Cryptography.SecureComputation
