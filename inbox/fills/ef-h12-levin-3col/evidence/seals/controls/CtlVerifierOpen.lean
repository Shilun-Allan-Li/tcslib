import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.Verifier
set_option autoImplicit false
open Complexity
example (q : PolyExpr) (x y : List Bool) : TCSlib.Cryptography.LevinHardness.certOf q x y = y ++ true :: List.replicate (q.eval x.length - y.length) false := rfl
