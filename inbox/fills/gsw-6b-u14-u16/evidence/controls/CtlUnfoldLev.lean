import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Leveled

/-! C6 control (gsw-6b-u14-u16): owner `GSW/Leveled.lean`, negative: `levelKey` read by `rfl`. Passes unsealed; must fail exactly once sealed. -/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

open BoolCircuit
open Encryption.PublicKey

example (P : Parameters) {L : ℕ} (pks : Fin (L + 1) → PublicKey P) (ss : Fin (L + 1) → Secret P)
    (R : LevelCoins P L) (d : Fin L) :
    levelKey P pks ss R d = evalKey P (pks d.succ) (ss d.castSucc) (R d) := rfl

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
