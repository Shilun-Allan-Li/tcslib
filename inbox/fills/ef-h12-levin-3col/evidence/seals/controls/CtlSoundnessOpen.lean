import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.Soundness
set_option autoImplicit false
open Complexity
example (K : ℕ) (mem : ℕ → Bool) : TCSlib.Cryptography.LevinHardness.gadgetFormula K mem = ((List.finRange ((2 * K) ^ 3)).filter fun c => mem c.val).map (TCSlib.Cryptography.LevinHardness.clauseEquiv K) := rfl
