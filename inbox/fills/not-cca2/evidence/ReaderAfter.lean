import TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity

open Complexity TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.Composability

attribute [local irreducible] FixedLengthScheme.inLens FixedLengthScheme.outLens

example (S : FixedLengthScheme) (atk : Attack) (b : Bool) (n : ℕ)
    (k : List Bool) (mm : Fin (n + n) → Bool) : True := by
  have hh := FixedLengthScheme.indImpl_challenge_none S atk b n k mm
  have hh' := heq_of_eq hh
  exact True.intro
