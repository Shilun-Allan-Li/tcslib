import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.CircuitWitness
set_option autoImplicit false
open Complexity
attribute [local irreducible] TCSlib.Cryptography.LevinHardness.retarget
example (d : List Bool) (v : ℕ) : TCSlib.Cryptography.LevinHardness.retarget d v = TCSlib.Cryptography.LevinHardness.descPrefix d ++ BoolCircuit.encodeNat v := rfl
example (d : List Bool) (v : ℕ) : TCSlib.Cryptography.LevinHardness.retarget d v = TCSlib.Cryptography.LevinHardness.descPrefix d ++ BoolCircuit.encodeNat v := TCSlib.Cryptography.LevinHardness.retarget_eq d v
