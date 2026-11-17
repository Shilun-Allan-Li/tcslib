import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Circular
set_option autoImplicit false
namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
open Encryption.PublicKey
-- Rule 10 control (neg): reads `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.WeakCircularSecure` of TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Circular from another file through its body
example (P : Parameters) (χ : LWE.Noise) {ρ : Type} [Fintype ρ] [Nonempty ρ] (D : FheView P → ρ → Bool) (ε : ℝ) :
    WeakCircularSecure P χ D ε ↔ distAdv (fheView P χ false) (fheView P χ true) D ≤ ε :=
  Iff.rfl
end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
