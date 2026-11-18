import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.Padding
set_option autoImplicit false
open Complexity
attribute [local irreducible] TCSlib.Cryptography.LevinHardness.padColWord
example (w : List Bool) (B : ℕ) : TCSlib.Cryptography.LevinHardness.padColWord w B = w ++ List.replicate (2 * B - w.length) false := rfl
example (w : List Bool) (B : ℕ) : TCSlib.Cryptography.LevinHardness.padColWord w B = w ++ List.replicate (2 * B - w.length) false := TCSlib.Cryptography.LevinHardness.padColWord_eq w B
