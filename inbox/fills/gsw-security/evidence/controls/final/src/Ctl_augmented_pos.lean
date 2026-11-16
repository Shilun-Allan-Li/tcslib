import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Scheme
import TCSlib.Cryptography.Hashing.SIS.Columns
import TCSlib.Cryptography.LWE.Experiments
import Mathlib.Tactic.Simps.Basic

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
open Encryption.PublicKey

example (P : LWE.Parameters)
    (pk : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) :
    Regev.augmented P pk = Fin.snoc pk.1.transpose pk.2 := Regev.augmented_eq P pk

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
