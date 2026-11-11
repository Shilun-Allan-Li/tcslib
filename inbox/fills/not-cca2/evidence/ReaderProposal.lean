import TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity

open Complexity TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.Composability

namespace TCSlib.Cryptography.Composability.FixedLengthScheme

/-- PROPOSED PROVIDER READER, NOT AN AUTHORIZED PRODUCTION CHANGE.
The first challenge query, transported to its declared input width, returns the
selected encryption transported to its declared answer width and records the
untransported ciphertext as state. The casts make the formula usable while the
foreign length definitions are sealed. This proof is a provider-side prototype:
it should be placed in OracleSecurity.lean, which owns these definitions. -/
theorem proposed_indImpl_challenge_none_cast (S : FixedLengthScheme)
    (atk : Attack) (b : Bool) (n : ℕ) (k : List Bool) (mm : Fin (n + n) → Bool) :
    S.indImpl atk b n k 2
      (cast (congrArg (fun d => Fin d → Bool) (S.inLens_two n)).symm mm) none =
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        let c := S.encryptAt n k (if b then (splitHalf mm).2 else (splitHalf mm).1) r
        .pure (cast (congrArg (fun d => Fin d → Bool) (S.outLens_two n)).symm c, some c) := by
  rfl

attribute [local irreducible] inLens outLens indImpl

/-- The proposed reader can be consumed by a generic equality operation under the
same length seal that blocks the published point reader. -/
example (S : FixedLengthScheme) (atk : Attack) (b : Bool) (n : ℕ)
    (k : List Bool) (mm : Fin (n + n) → Bool) : True := by
  have hh := proposed_indImpl_challenge_none_cast S atk b n k mm
  have hh' := heq_of_eq hh
  exact True.intro

#print axioms proposed_indImpl_challenge_none_cast

end TCSlib.Cryptography.Composability.FixedLengthScheme
