import TCSlib.Cryptography.Hashing.SIS.Universality
import TCSlib.Cryptography.Foundations.Probability
import TCSlib.Cryptography.Pseudorandom.Indistinguishability

namespace TCSlib.Cryptography.Hashing.SIS
open TCSlib.Cryptography.SIS (Parameters)

example (P : Parameters) (A : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus))
    (x : Fin P.columns → Bool) :
    hash P A x = A.mulVec (fun i => ((x i).toNat : ZMod P.modulus)) := rfl

end TCSlib.Cryptography.Hashing.SIS
