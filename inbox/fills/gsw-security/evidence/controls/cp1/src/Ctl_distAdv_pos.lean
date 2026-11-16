import TCSlib.Cryptography.Hashing.SIS.Universality
import TCSlib.Cryptography.Foundations.Probability
import TCSlib.Cryptography.Pseudorandom.Indistinguishability

namespace TCSlib.Cryptography.Hashing.SIS
open TCSlib.Cryptography.SIS (Parameters)

example {σ τ γ ρ : Type} [Fintype σ] [Fintype τ] [Fintype ρ] (X : σ → γ) (Y : τ → γ)
    (D : γ → ρ → Bool) : distAdv X Y D = |acceptProb X D - acceptProb Y D| := distAdv_def X Y D

end TCSlib.Cryptography.Hashing.SIS
