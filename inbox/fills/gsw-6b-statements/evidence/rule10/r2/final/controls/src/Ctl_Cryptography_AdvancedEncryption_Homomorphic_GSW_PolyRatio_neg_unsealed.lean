import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.PolyRatio
set_option autoImplicit false
namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
open Complexity
open Encryption.PublicKey
-- Rule 10 control (neg): reads `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.pBoot` of TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.PolyRatio from another file through its body
example (F : LWE.Family) :
    pBoot F =
      .mul (.mul (.mul (.mul (.const (2 ^ 70)) F.residueBits)
          (.pow (.mul (.add F.dimensionBound (.const 1)) F.residueBits) 19))
        (.pow (.add (.add F.residueBits (.mul (.add F.dimensionBound (.const 1)) F.residueBits))
          (.const 3)) 4))
        F.samplesBound :=
  rfl
end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
