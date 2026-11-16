import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Scheme
import TCSlib.Cryptography.Hashing.SIS.Columns
import TCSlib.Cryptography.LWE.Experiments
import Mathlib.Tactic.Simps.Basic

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
open Encryption.PublicKey

example (P : TCSlib.Cryptography.SIS.Parameters) (N : ℕ)
    (A : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus))
    (R : Matrix (Fin P.columns) (Fin N) Bool) (i : Fin P.dimension) (j : Fin N) :
    Hashing.SIS.hashColumns P N A R i j = Hashing.SIS.hash P A (fun c => R c j) i := Hashing.SIS.hashColumns_apply P N A R i j

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
