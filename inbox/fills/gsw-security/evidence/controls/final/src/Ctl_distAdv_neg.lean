import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Scheme
import TCSlib.Cryptography.Hashing.SIS.Columns
import TCSlib.Cryptography.LWE.Experiments
import Mathlib.Tactic.Simps.Basic

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
open Encryption.PublicKey

example {σ τ γ ρ : Type} [Fintype σ] [Fintype τ] [Fintype ρ] (X : σ → γ) (Y : τ → γ)
    (D : γ → ρ → Bool) : distAdv X Y D = |acceptProb X D - acceptProb Y D| := rfl

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
