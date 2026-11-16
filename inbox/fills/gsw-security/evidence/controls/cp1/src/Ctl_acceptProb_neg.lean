import TCSlib.Cryptography.Hashing.SIS.Universality
import TCSlib.Cryptography.Foundations.Probability
import TCSlib.Cryptography.Pseudorandom.Indistinguishability

namespace TCSlib.Cryptography.Hashing.SIS
open TCSlib.Cryptography.SIS (Parameters)

example {σ γ ρ : Type} [Fintype σ] [Fintype ρ] (X : σ → γ) (D : γ → ρ → Bool) :
    acceptProb X D = uprob fun z : σ × ρ => D (X z.1) z.2 = true := rfl

end TCSlib.Cryptography.Hashing.SIS
