import Lean
import TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF
import Mathlib.Tactic.Simps.Basic

example (z : List Bool) : Complexity.NUPPT.inArg z =
    Complexity.pairSndD (Complexity.pairFstD (Complexity.pairFstD z)) := by
  rfl
