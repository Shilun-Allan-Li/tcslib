import Lean
import TCSlib.Cryptography.Authentication.Defs
import TCSlib.Cryptography.Authentication.Signatures.Defs
import TCSlib.Cryptography.Authentication.Encoding
import TCSlib.Cryptography.Authentication.MAC.Defs
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRG
import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.FromPermutation
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Run
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM
import TCSlib.Cryptography.Authentication.MAC.FromPRF
import TCSlib.Cryptography.Authentication.Signatures.Lamport
import TCSlib.Cryptography.Hashing.FromDiscreteLog
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.CodecReaders
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.CollisionGame
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.CollisionHandler
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.FixedGame
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.ForwardGame
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.ForwardHandler
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.OneQuerySampling
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.OneQuery

set_option maxHeartbeats 0
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HashSignBatchingPilot

theorem negative (l : ℕ) (w : List Bool) (i : Fin l) : TCSlib.Cryptography.padFin l w i = w.getD i false := rfl

theorem positive (l : ℕ) (w : List Bool) (i : Fin l) : TCSlib.Cryptography.padFin l w i = w.getD i false := TCSlib.Cryptography.padFin_apply l w i

end HashSignBatchingPilot

