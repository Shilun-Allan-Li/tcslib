import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.ColoringGraph
set_option autoImplicit false
open Complexity
attribute [local irreducible] TCSlib.Cryptography.LevinHardness.colorInst
example (s : List Bool) : TCSlib.Cryptography.LevinHardness.colorInst s = if TCSlib.Cryptography.LevinHardness.goodS s then TCSlib.Cryptography.encGraph (TCSlib.Cryptography.LevinHardness.gadgetGraph s.length (TCSlib.Cryptography.LevinHardness.memS s)) else TCSlib.Cryptography.encGraph TCSlib.Cryptography.LevinHardness.k4 := rfl
example (s : List Bool) : TCSlib.Cryptography.LevinHardness.colorInst s = if TCSlib.Cryptography.LevinHardness.goodS s then TCSlib.Cryptography.encGraph (TCSlib.Cryptography.LevinHardness.gadgetGraph s.length (TCSlib.Cryptography.LevinHardness.memS s)) else TCSlib.Cryptography.encGraph TCSlib.Cryptography.LevinHardness.k4 := TCSlib.Cryptography.LevinHardness.colorInst_eq s
