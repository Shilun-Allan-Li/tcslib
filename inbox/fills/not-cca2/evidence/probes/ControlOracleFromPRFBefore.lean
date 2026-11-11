import Lean
import TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF
import Mathlib.Tactic.Simps.Basic

example (S : TCSlib.Cryptography.Composability.FixedLengthScheme) (n : ℕ) :
    S.inLens n 2 = n + n := by
  rfl
