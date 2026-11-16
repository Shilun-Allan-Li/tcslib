/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.SpecialEncryptionMulti
import TCSlib.Complexity.Randomized.Closure
import TCSlib.Cryptography.Asymptotic.Sampling

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Advice and averaging for a slice-encryption reduction

A polynomial-time reconstruction can use polynomial-length advice without depending
on the challenge key or nonces. The machine below keeps the original distinguisher's
random tape and runs it at the same security parameter.

## Main definitions

There are no new definitions.

## Main results

* `exists_adviceReduction`: a reconstruction with fixed advice is a non-uniform PPT test.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Theorem 163.7 and the hybrid argument in §6.2.3.
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReduction

open Complexity Turing TCSlib.Cryptography

/-- For a polynomial-time `rebuild` and advice `β n` of polynomially bounded length,
there is one non-uniform PPT test that runs `D` on
`rebuild ⟨1^n, ⟨challenge, β n⟩⟩`, at parameter `n`, with the same random bits.
[PS10, Theorem 163.7, non-uniform reduction]

**Proof sketch.** Use the existing parameter-aware composition constructor to run the
reconstruction before `D`, then the advice constructor to fix `β`. The published coin
congruence preserves the entire tape, so the resulting tests agree pointwise. -/
theorem exists_adviceReduction (D : NUPPT) {rebuild : List Bool → List Bool}
    (hRebuild : PolyTimeComputable rebuild) (β : ℕ → List Bool) (b : PolyExpr)
    (hβ : ∀ n, (β n).length ≤ b.eval n) :
    ∃ R : NUPPT, ∃ hcoins : R.coins = D.coins,
      ∀ n challenge (r : D.Coins n),
        R.distinguisherL n challenge (NUPPT.coinsCongr hcoins.symm n r) =
          D.distinguisherL n
            (rebuild (pairEncode (List.replicate n true) (pairEncode challenge (β n)))) r := by
  obtain ⟨C, hCc, _, _, hC⟩ :=
    D.exists_compParam hRebuild polyTimeComputable_pairSndD
  obtain ⟨R, hRc, hR⟩ := C.exists_withAdvice β b hβ
  refine ⟨R, hRc.trans hCc, ?_⟩
  intro n challenge r
  rw [NUPPT.distinguisherL_eq, NUPPT.distinguisherL_eq, NUPPT.runAt_eq,
    NUPPT.runAt_eq, NUPPT.coinsCongr_ofFn, hR, hC, pairSndD_pairEncode,
    NUPPT.advInput_eq]

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReduction
