import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.ColoringParse
set_option autoImplicit false
open Complexity
attribute [local irreducible] TCSlib.Cryptography.LevinHardness.clauseRec
example (C : Std.Sat.CNF.Clause ℕ) : TCSlib.Cryptography.LevinHardness.clauseRec C = true :: Std.Sat.CNF.serializeClause C := rfl
example (C : Std.Sat.CNF.Clause ℕ) : TCSlib.Cryptography.LevinHardness.clauseRec C = true :: Std.Sat.CNF.serializeClause C := TCSlib.Cryptography.LevinHardness.clauseRec_eq C
