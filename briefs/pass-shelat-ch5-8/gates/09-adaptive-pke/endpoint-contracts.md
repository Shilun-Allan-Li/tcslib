# Gate 09 · checked endpoint contract probes

This scratch module verifies the older-ciphertext refusal and both shifted single-bit constructions through the public interfaces. It also checks the proposed later endpoint and lifting proposition types.

```lean
import TCSlib.Cryptography.Encryption.PublicKey

set_option relaxedAutoImplicit false
set_option autoImplicit false

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Candidates
open TCSlib.Cryptography.Composability TCSlib.Cryptography.Games

attribute [local irreducible] FixedLengthPKScheme.adaptiveIndImpl FixedLengthPKScheme.indImpl
attribute [local irreducible] FixedLengthPKScheme.inLens FixedLengthPKScheme.outLens
attribute [local irreducible] FixedLengthPKScheme.adaptiveIndGame FixedLengthPKScheme.AdaptiveINDSecure
attribute [local irreducible] TrapdoorCollection.shiftParameter TrapdoorCollection.glPad
attribute [local irreducible] rsaTrapdoor rabinBlumTrapdoor

-- Every issued challenge is refused, even when a more recent ciphertext was issued.
example (S : FixedLengthPKScheme) (b : Bool) (n : ℕ) (pk sk : List Bool) (cap : ℕ)
    (q : (S.indSpec n).dom 0) (latest : Fin (S.ctLen.eval n) → Bool) :
    S.adaptiveIndImpl .cca2 b n pk sk cap 0 q [latest, cast (S.indSpec_decDom n) q] =
      .pure (zeroBits _, [latest, cast (S.indSpec_decDom n) q]) := by
  exact S.adaptiveIndImpl_dec_issued _ _ _ _ _ _ _ _ (by simp)

-- The width and hardness transports meet the existing Goldreich–Levin PKE API.
theorem rsaShiftedSingleBitProbe (H : ArithmeticFP) (hRSA : RSAAssumption) :
    ∃ B : BitPublicKeyScheme, B.SingleBitSecure := by
  have h := (rsaTrapdoor H).shiftParameter_oneWay 2 (rsaTrapdoor_oneWay H hRSA)
  obtain ⟨E, hE⟩ := h.exists_glPad_singleBitSecure
    (.mul (.const 2) (.add .var (.const 2))) (rsaTrapdoor_shiftParameter_encD_length H)
  exact ⟨_, hE⟩

theorem rabinShiftedSingleBitProbe (H : ArithmeticFP) (hD : BlumDensity) (hF : FactoringAssumption) :
    ∃ B : BitPublicKeyScheme, B.SingleBitSecure := by
  have h := (rabinBlumTrapdoor H).shiftParameter_oneWay 3 (rabinBlumTrapdoor_oneWay H hD hF)
  obtain ⟨E, hE⟩ := h.exists_glPad_singleBitSecure
    (.mul (.const 2) (.add .var (.const 3))) (rabinBlumTrapdoor_shiftParameter_encD_length H)
  exact ⟨_, hE⟩

-- Proposed endpoint types for review. These commands typecheck the propositions.
example : Prop := ∀ (_ : ArithmeticFP), RSAAssumption →
  ∃ S : FixedLengthPKScheme, S.msgLen = PolyExpr.var ∧ S.AdaptiveINDSecure .cpa

example : Prop := ∀ (_ : ArithmeticFP), BlumDensity → FactoringAssumption →
  ∃ S : FixedLengthPKScheme, S.msgLen = PolyExpr.var ∧ S.AdaptiveINDSecure .cpa

example : Prop := ∃ S : FixedLengthPKScheme, S.msgLen = PolyExpr.var ∧ S.AdaptiveINDSecure .cca2

-- Proposed supporting lifts for the audit's feasibility review.
example : Prop := ∀ S : FixedLengthPKScheme, S.INDSecure .cpa → S.AdaptiveINDSecure .cpa
example : Prop := ∀ S : FixedLengthPKScheme, S.INDSecure .cca2 → S.AdaptiveINDSecure .cca2

#print axioms FixedLengthPKScheme.adaptiveIndImpl_challenge_encrypt
#print axioms FixedLengthPKScheme.adaptiveIndGame_one
#print axioms FixedLengthPKScheme.AdaptiveINDSecure.single
#print axioms TrapdoorCollection.shiftParameter_oneWay
#print axioms rsaTrapdoor_shiftParameter_encD_length
#print axioms rabinBlumTrapdoor_shiftParameter_encD_length
#print axioms rsaShiftedSingleBitProbe
#print axioms rabinShiftedSingleBitProbe
```
