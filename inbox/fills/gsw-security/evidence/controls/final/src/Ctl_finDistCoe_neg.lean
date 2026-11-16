import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Scheme
import TCSlib.Cryptography.Hashing.SIS.Columns
import TCSlib.Cryptography.LWE.Experiments
import Mathlib.Tactic.Simps.Basic

namespace TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
open Encryption.PublicKey

example {α : Type} [Fintype α] (p : TCSlib.InformationTheory.FinDist α) (a : α) :
    p a = p.prob a := rfl

end TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
