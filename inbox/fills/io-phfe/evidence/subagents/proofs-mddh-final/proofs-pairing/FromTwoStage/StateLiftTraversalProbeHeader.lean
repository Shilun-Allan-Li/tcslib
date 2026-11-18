import TCSlib.Cryptography.Games.Probability

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption

open TCSlib.Cryptography.Games

/-- Proposed logical traversal identity for specializing a stateful loop to unchanged state.
No proof is supplied before native reuse searches. -/
theorem stateT_mapM_lift {alpha beta sigma : Type}
    (f : alpha → ProbComp beta) (xs : List alpha) (st : sigma) :
    (List.mapM (m := StateT sigma ProbComp)
        (fun x => StateT.lift (f x)) xs).run st =
      (List.mapM f xs).bind fun ys => .pure (ys, st) := sorry

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption
