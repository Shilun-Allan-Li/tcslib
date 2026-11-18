import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.Verifier
set_option autoImplicit false
open Complexity
attribute [local irreducible] TCSlib.Cryptography.LevinHardness.certOf
example (q : PolyExpr) (x y : List Bool) : TCSlib.Cryptography.LevinHardness.certOf q x y = y ++ true :: List.replicate (q.eval x.length - y.length) false := rfl
example (q : PolyExpr) (x y : List Bool) : TCSlib.Cryptography.LevinHardness.certOf q x y = y ++ true :: List.replicate (q.eval x.length - y.length) false := TCSlib.Cryptography.LevinHardness.certOf_eq q x y
