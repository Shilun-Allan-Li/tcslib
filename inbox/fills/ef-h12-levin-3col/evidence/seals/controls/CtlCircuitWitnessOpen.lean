import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.CircuitWitness
set_option autoImplicit false
open Complexity
example (d : List Bool) (v : ℕ) : TCSlib.Cryptography.LevinHardness.retarget d v = TCSlib.Cryptography.LevinHardness.descPrefix d ++ BoolCircuit.encodeNat v := rfl
