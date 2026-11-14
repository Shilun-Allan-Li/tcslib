import Lean
import TCSlib.Cryptography.Authentication
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.CodecReaders
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.CollisionGame
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.CollisionHandler
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.FixedGame
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.ForwardGame
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.ForwardHandler
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.OneQuery
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign.OneQuerySampling

set_option maxHeartbeats 0
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let names : Array Name := #[`Complexity.NUPPT.Uniform.runAtL_eq, `Complexity.NUPPT.Uniform.runAt_eq, `Equiv.apply_symm_apply, `TCSlib.Cryptography.Authentication.SignatureScheme.forgeGame_eq, `TCSlib.Cryptography.Authentication.SignatureScheme.forgerCodec_eq_bitCodec, `TCSlib.Cryptography.Authentication.SignatureScheme.signImpl_eq, `TCSlib.Cryptography.Games.InteractiveHandler.finA_finInput, `TCSlib.Cryptography.Games.InteractiveHandler.rAns_input, `TCSlib.Cryptography.Games.InteractiveHandler.rL_input, `TCSlib.Cryptography.Games.InteractiveHandler.rS_input, `TCSlib.Cryptography.Games.InteractiveHandler.rU_finInput, `TCSlib.Cryptography.Games.InteractiveHandler.rU_input, `TCSlib.Cryptography.Games.InteractiveHandler.rW_finInput, `TCSlib.Cryptography.Games.InteractiveHandler.rW_input, `TCSlib.Cryptography.Games.InteractiveHandler.rX_input]
  for n in names do
    match env.find? n with
    | some (.thmInfo _) => IO.println s!"EXPLICIT_ALIAS_THEOREM {n}"
    | _ => throwError "Explicit scan alias is not a theorem: {n}"
  IO.println s!"EXPLICIT_ALIAS_DONE {names.size}"
