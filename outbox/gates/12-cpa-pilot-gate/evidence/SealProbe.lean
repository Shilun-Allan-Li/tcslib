import TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA
open TCSlib.Cryptography TCSlib.Cryptography.Composability Complexity Turing
attribute [local irreducible] TCSlib.Cryptography.PublicKeyScheme.padded
  TCSlib.Cryptography.BitPublicKeyScheme.bitwise
  TCSlib.Cryptography.Composability.FixedLengthPKScheme.ofPadded
  TCSlib.Cryptography.Composability.FixedLengthPKScheme.INDSecure
  TCSlib.Cryptography.Composability.FixedLengthPKScheme.AdaptiveINDSecure
  TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure Complexity.NUPPT.runAt Turing.pairEncode
  Complexity.pairFstD

theorem probe_adaptive {S : BitPublicKeyScheme} (h : S.SingleBitSecure) (L : PolyExpr)
    (hL : ∀ n (rg : S.bitwise.gen.Coins n) (m : Fin n → Bool) (re : S.bitwise.enc.Coins n),
      2 * (S.bitwise.enc.runAt n (pairEncode (pairFstD (S.bitwise.gen.runAt n [] rg))
        (List.ofFn m)) re).length + 2 ≤ L.eval n)
    (hmsg : ∀ n, n ≤ L.eval n) : (S.bitwise.padded L hL hmsg).AdaptiveINDSecure .cpa :=
  (h.bitwise_padded_cpa L hL hmsg).adaptive_cpa

theorem probe_exists {S : BitPublicKeyScheme} (h : S.SingleBitSecure) :
    ∃ S' : FixedLengthPKScheme, S'.msgLen = .var ∧ S'.gen = S.gen ∧
      S'.AdaptiveINDSecure .cpa := by
  obtain ⟨L, hL, hmsg⟩ := S.bitwise.exists_padBound
  exact ⟨S.bitwise.padded L hL hmsg, PublicKeyScheme.padded_msgLen _ _ _ _,
    (PublicKeyScheme.padded_gen _ _ _ _).trans (BitPublicKeyScheme.bitwise_gen S),
    h.bitwise_padded_adaptive_cpa L hL hmsg⟩

-- control: reads `bitwise` through its body; must FAIL sealed
example (S : BitPublicKeyScheme) : S.bitwise.gen = S.gen := rfl
