import Lean
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.ChallengeSim

example (ℓ : ℕ) (w : List Bool) (i : Fin ℓ) :
    TCSlib.Cryptography.padFin ℓ w i = w.getD i false := by
  rfl
