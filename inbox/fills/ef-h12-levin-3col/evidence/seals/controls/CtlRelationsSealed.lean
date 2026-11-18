import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.Relations
set_option autoImplicit false
open Complexity
attribute [local irreducible] TCSlib.Cryptography.LevinHardness.R_CKT
example (d u : List Bool) : TCSlib.Cryptography.LevinHardness.R_CKT d u ↔ ∃ (n : ℕ) (C : BoolCircuit.DAGCircuit n), C.IsFaninTwo ∧ C.encode = d ∧ C.eval (fun i => u.getD i false) = true := Iff.rfl
example (d u : List Bool) : TCSlib.Cryptography.LevinHardness.R_CKT d u ↔ ∃ (n : ℕ) (C : BoolCircuit.DAGCircuit n), C.IsFaninTwo ∧ C.encode = d ∧ C.eval (fun i => u.getD i false) = true := TCSlib.Cryptography.LevinHardness.R_CKT_iff d u
