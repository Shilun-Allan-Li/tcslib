import Lean
import TCSlib.Cryptography.Asymptotic.HardCoreLoops
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRG
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.Hybrid
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.HybridLemmas
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.ReductionMachine
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM

example (x a : List Bool) :
    Turing.pairEncode x a = (x.flatMap fun b => [b, b]) ++ [false, true] ++ a := by
  rfl
