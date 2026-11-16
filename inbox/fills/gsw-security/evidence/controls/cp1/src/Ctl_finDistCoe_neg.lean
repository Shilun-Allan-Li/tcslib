import TCSlib.Cryptography.Hashing.SIS.Universality
import TCSlib.Cryptography.Foundations.Probability
import TCSlib.Cryptography.Pseudorandom.Indistinguishability

namespace TCSlib.Cryptography.Hashing.SIS
open TCSlib.Cryptography.SIS (Parameters)

example {α : Type} [Fintype α] (p : TCSlib.InformationTheory.FinDist α) (a : α) :
    p a = p.prob a := rfl

end TCSlib.Cryptography.Hashing.SIS
