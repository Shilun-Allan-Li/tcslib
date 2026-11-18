import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.ColoringWitness
set_option autoImplicit false
open Complexity
example (s a : List Bool) : TCSlib.Cryptography.LevinHardness.colorWord s a = TCSlib.Cryptography.encColoring (fun u : Fin (TCSlib.Cryptography.LevinHardness.gadgetN s.length) => TCSlib.Cryptography.LevinHardness.gadgetColor s.length (fun v => a.getD v false) u) := rfl
