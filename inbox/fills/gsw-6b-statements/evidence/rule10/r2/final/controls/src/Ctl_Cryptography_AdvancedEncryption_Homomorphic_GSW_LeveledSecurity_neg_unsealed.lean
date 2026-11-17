import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.LeveledSecurity
set_option autoImplicit false
namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
open Encryption.PublicKey
-- Rule 10 control (neg): reads `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.challengeDist` of TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.LeveledSecurity from another file through its body
example (P : Parameters) (χ : LWE.Noise) (L : ℕ) {ρ : Type}
    (D : LeveledView P L → ρ → Bool) (v : PublicKey P × Ciphertext P)
    (c : LeveledSeeds P χ L × ρ) :
    challengeDist P χ L D v c =
      D (Function.update (fun d => (Regev.keygen P.lwe χ (c.1.1 d)).1) 0 v.1,
        fun e j => encrypt P (Regev.keygen P.lwe χ (c.1.1 e.succ)).1 false (c.1.2.1 e j), v.2)
        c.2 :=
  rfl
end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
