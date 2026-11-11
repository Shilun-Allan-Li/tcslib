import Lean
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity
import TCSlib.Cryptography.Games.Efficiency
import TCSlib.Cryptography.Asymptotic.OneWayLemmas
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
import TCSlib.Cryptography.Asymptotic.CollectionsHelpers
import TCSlib.Cryptography.Asymptotic.CollectionsLemmas
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Run
import TCSlib.Complexity.ClassNP.PolyTimePrefix

example (n : ℕ) (z ω s : List Bool) (i : Fin 2) (x L : List Bool) :
    TCSlib.Cryptography.Games.InteractiveHandler.input n z ω s i x L =
      Turing.pairEncode (Turing.pairEncode (List.replicate n true) (Turing.pairEncode z ω))
        (Turing.pairEncode s (Turing.pairEncode (Turing.pairEncode (List.replicate i true) x) L)) := by
  rfl
