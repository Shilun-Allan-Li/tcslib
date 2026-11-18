import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.ColoringGraph
set_option autoImplicit false
open Complexity
example (s : List Bool) : TCSlib.Cryptography.LevinHardness.colorInst s = if TCSlib.Cryptography.LevinHardness.goodS s then TCSlib.Cryptography.encGraph (TCSlib.Cryptography.LevinHardness.gadgetGraph s.length (TCSlib.Cryptography.LevinHardness.memS s)) else TCSlib.Cryptography.encGraph TCSlib.Cryptography.LevinHardness.k4 := rfl
