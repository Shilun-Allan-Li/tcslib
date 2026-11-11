import Lean
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Games

example (S : TCSlib.Cryptography.Composability.FixedLengthPKScheme) :
    TCSlib.Cryptography.Composability.AdaptiveCPA.acDout S 1 = S.ctLen := by
  rfl
