
/-! Liveness pair (gsw-6b-u15-u17, C6, owner LeveledSecurity.lean), appended to the owner's own probe:
a foreign definition read by `rfl` (negative: closes unsealed, fails exactly once sealed) and the
same fact through its published reader (positive: closes sealed). -/

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
open Encryption.PublicKey

-- NEG levelKey by rfl
example (P : Parameters) {L : ℕ} (pks : Fin (L + 1) → PublicKey P) (ss : Fin (L + 1) → Secret P)
    (R : LevelCoins P L) (d : Fin L) :
    levelKey P pks ss R d = evalKey P (pks d.succ) (ss d.castSucc) (R d) :=
  rfl
-- POS levelKey through levelKey_eq
example (P : Parameters) {L : ℕ} (pks : Fin (L + 1) → PublicKey P) (ss : Fin (L + 1) → Secret P)
    (R : LevelCoins P L) (d : Fin L) :
    levelKey P pks ss R d = evalKey P (pks d.succ) (ss d.castSucc) (R d) :=
  levelKey_eq P pks ss R d

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
