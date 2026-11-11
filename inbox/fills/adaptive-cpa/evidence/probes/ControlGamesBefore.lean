import Lean
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveSecurity
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Hybrid
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Handler

example (S : TCSlib.Cryptography.Composability.FixedLengthPKScheme) (n : ℕ) :
    S.inLens n 0 = S.ctLen.eval n := by
  rfl
