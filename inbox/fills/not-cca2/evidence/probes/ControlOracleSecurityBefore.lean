import Lean
import TCSlib.Cryptography.Games.BitCodec
import TCSlib.Cryptography.Games.Advantage
import TCSlib.Cryptography.Encryption.PrivateKey.Scheme
import TCSlib.Cryptography.Foundations.Negligible

example (d : ℕ) (j : Fin d) : TCSlib.Cryptography.Games.zeroBits d j = false := by
  rfl
