import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.Gadget
set_option autoImplicit false
open Complexity
attribute [local irreducible] TCSlib.Cryptography.LevinHardness.gadgetN
example (K : ℕ) : TCSlib.Cryptography.LevinHardness.gadgetN K = 3 + 2 * K + 6 * (2 * K) ^ 3 := rfl
example (K : ℕ) : TCSlib.Cryptography.LevinHardness.gadgetN K = 3 + 2 * K + 6 * (2 * K) ^ 3 := TCSlib.Cryptography.LevinHardness.gadgetN_eq K
