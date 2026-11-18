import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.Gadget
set_option autoImplicit false
open Complexity
example (K : ℕ) : TCSlib.Cryptography.LevinHardness.gadgetN K = 3 + 2 * K + 6 * (2 * K) ^ 3 := rfl
