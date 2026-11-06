import TCSlib.Cryptography.Asymptotic.HardCoreCollection

set_option autoImplicit false

open Complexity Turing TCSlib.Cryptography

-- SEAL-LINE

variable (P : PermCollection) (m : PolyExpr)
  (henc : ∀ n (r : P.gen.Coins n) (x : P.D (P.index n r)), (P.encD (P.index n r) x).length = m.eval n)
  (i : List Bool)
