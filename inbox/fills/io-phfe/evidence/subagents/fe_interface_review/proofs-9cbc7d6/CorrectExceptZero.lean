/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Defs.Correctness
import TCSlib.Cryptography.Games.Hopping

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Proof draft: perfect FE correctness gives zero error

The proof uses the existing all-outputs-to-zero-probability theorem. It introduces no
helper or interface statement change. The draft suffix avoids collision with the existing
admitted declaration; replace only that declaration's body when integrating.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw

open TCSlib.Cryptography.Games

variable {C : FnClass} (S : FEScheme.Raw C)

/-- Perfect correctness makes the failure predicate impossible on every honest output.
[GJLS21, Definition 4.2]. This is a proof draft for Correct.correctExcept_zero. -/
theorem Correct.correctExcept_zero_draft (h : S.Correct) : S.CorrectExcept 0 :=
  (S.correctExcept_iff 0).2 fun κ f x y =>
    (ProbComp.prob_eq_zero_of_allOutputs
      (OracleComp.AllOutputs.mono (fun _ hout hne => hne hout)
        (S.correct_iff.1 h κ f x y))).le

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.FEScheme.Raw
