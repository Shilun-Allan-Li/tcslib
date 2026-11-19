
/-! Liveness pair (gsw-6b-u18-u19, C6, owner PolyRatio.lean), appended to the owner's own probe: a
foreign definition read by `rfl` (negative: closes unsealed, fails exactly once sealed) and the
same fact through its published reader (positive: closes sealed). -/

-- NEG bootNoise by rfl
example (P : TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Parameters) (β : ℕ) :
    TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.bootNoise P β = 4 ^ (TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.decDepth P + 1) * (2 * (P.columns * β)) :=
  rfl
-- POS bootNoise through bootNoise_eq
example (P : TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Parameters) (β : ℕ) :
    TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.bootNoise P β = 4 ^ (TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.decDepth P + 1) * (2 * (P.columns * β)) :=
  TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.bootNoise_eq P β
