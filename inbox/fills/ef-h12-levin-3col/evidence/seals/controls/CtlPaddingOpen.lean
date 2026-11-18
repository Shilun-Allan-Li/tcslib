import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.Padding
set_option autoImplicit false
open Complexity
example (w : List Bool) (B : ℕ) : TCSlib.Cryptography.LevinHardness.padColWord w B = w ++ List.replicate (2 * B - w.length) false := rfl
