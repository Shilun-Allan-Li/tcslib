import Lean
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveSecurity
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Hybrid
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Handler
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Games
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Reduction
import TCSlib.Cryptography.Games.Advantage
import TCSlib.Cryptography.Games.Efficiency
import TCSlib.Cryptography.Asymptotic.ReductionSupport

example (S : TCSlib.Cryptography.Composability.FixedLengthPKScheme) (cap : Complexity.PolyExpr)
    (ist : ℕ → ℕ) :
    (TCSlib.Cryptography.Composability.AdaptiveCPA.acHandler S cap ist).perCall = .const 1 := by
  rfl
