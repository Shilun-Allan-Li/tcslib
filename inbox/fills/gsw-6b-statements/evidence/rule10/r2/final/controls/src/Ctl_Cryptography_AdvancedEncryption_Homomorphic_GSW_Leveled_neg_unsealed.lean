import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Leveled
set_option autoImplicit false
namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
open BoolCircuit
open Encryption.PublicKey
-- Rule 10 control (neg): reads `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.levelKey` of TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Leveled from another file through its body
example (P : Parameters) {L : ℕ} (pks : Fin (L + 1) → PublicKey P)
    (ss : Fin (L + 1) → Secret P) (R : LevelCoins P L) (d : Fin L) :
    levelKey P pks ss R d = evalKey P (pks d.succ) (ss d.castSucc) (R d) :=
  rfl
end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
