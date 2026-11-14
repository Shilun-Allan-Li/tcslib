import Lean
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.CollisionHandler
import TCSlib.Cryptography.Games.Bridges.Experiments

set_option maxHeartbeats 0
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HashSignSensitivity

theorem negative (S : TCSlib.Cryptography.Authentication.SignatureScheme) (c : List Bool) : TCSlib.Cryptography.Authentication.HashSignFill.collisionKey S c = S.gen.output (Complexity.NUPPT.layout (Complexity.pairFstD c) [] [] ((Complexity.pairSndD (Complexity.pairSndD c)).take (S.gen.coins.eval (Complexity.pairFstD c).length))) := rfl

theorem positive (S : TCSlib.Cryptography.Authentication.SignatureScheme) (c : List Bool) : TCSlib.Cryptography.Authentication.HashSignFill.collisionKey S c = S.gen.output (Complexity.NUPPT.layout (Complexity.pairFstD c) [] [] ((Complexity.pairSndD (Complexity.pairSndD c)).take (S.gen.coins.eval (Complexity.pairFstD c).length))) := TCSlib.Cryptography.Authentication.HashSignFill.collisionKey_eq S c

end HashSignSensitivity

