import Lean
import TCSlib.Cryptography.Authentication.Signatures.Lamport
import TCSlib.Cryptography.Authentication.Signatures.Defs
import TCSlib.Cryptography.Hashing.CollisionResistant
import TCSlib.Cryptography.Authentication.Encoding
import TCSlib.Cryptography.Asymptotic.CollectionsLemmas

set_option maxHeartbeats 0
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HashSignSensitivity

theorem negative (l : ℕ) (w : List Bool) (i : Fin l) : TCSlib.Cryptography.padFin l w i = w.getD i false := rfl

theorem positive (l : ℕ) (w : List Bool) (i : Fin l) : TCSlib.Cryptography.padFin l w i = w.getD i false := TCSlib.Cryptography.padFin_apply l w i

end HashSignSensitivity

