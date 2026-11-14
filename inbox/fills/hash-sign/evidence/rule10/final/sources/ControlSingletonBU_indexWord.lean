import Lean
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.ForwardHandler
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.OneQuerySampling

set_option maxHeartbeats 0
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HashSignSensitivity

theorem negative (H : TCSlib.Cryptography.Authentication.CRH) (u ω : List Bool) : TCSlib.Cryptography.Authentication.HashSignForward.indexWord H u ω = H.gen.output (Complexity.NUPPT.layout u [] [] ω) := rfl

theorem positive (H : TCSlib.Cryptography.Authentication.CRH) (u ω : List Bool) : TCSlib.Cryptography.Authentication.HashSignForward.indexWord H u ω = H.gen.output (Complexity.NUPPT.layout u [] [] ω) := TCSlib.Cryptography.Authentication.HashSignForward.indexWord_eq H u ω

end HashSignSensitivity

