import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.DecryptFormula
open TCSlib.Cryptography
open TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
abbrev TP (q ℓ : ℕ) (hq : 2 ≤ q) (hℓ : q ≤ 2 ^ ℓ) : Parameters := ⟨⟨1, 2, q, hq⟩, ℓ, hℓ⟩
abbrev P4 : Parameters := TP 4 3 (by decide) (by decide)
example : DecidableEq (Ciphertext P4) := inferInstance
example : Decidable (∀ b : Bool, gadget P4 = gadget P4) := inferInstance
example (M : Ciphertext P4): Decidable (∀ b : Bool, M = M) := inferInstance
