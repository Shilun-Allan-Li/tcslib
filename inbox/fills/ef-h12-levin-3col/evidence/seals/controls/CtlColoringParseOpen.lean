import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.ColoringParse
set_option autoImplicit false
open Complexity
example (C : Std.Sat.CNF.Clause ℕ) : TCSlib.Cryptography.LevinHardness.clauseRec C = true :: Std.Sat.CNF.serializeClause C := rfl
