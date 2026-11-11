import TCSlib.Cryptography.Implications.PublicKey
open TCSlib.Cryptography TCSlib.Cryptography.Composability TCSlib.Cryptography.Candidates Complexity
attribute [local irreducible] TCSlib.Cryptography.Candidates.rsaTrapdoor
  TCSlib.Cryptography.Candidates.rabinBlumTrapdoor
  TCSlib.Cryptography.TrapdoorCollection.shiftParameter
  TCSlib.Cryptography.TrapdoorCollection.glPad
  TCSlib.Cryptography.TrapdoorCollection.tdpBitScheme
  TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure
  TCSlib.Cryptography.BitPublicKeyScheme.bitwise
  TCSlib.Cryptography.PublicKeyScheme.padded
  TCSlib.Cryptography.Composability.FixedLengthPKScheme.AdaptiveINDSecure
  TCSlib.Cryptography.Candidates.RSAAssumption
  TCSlib.Cryptography.Candidates.FactoringAssumption
  TCSlib.Cryptography.Candidates.BlumDensity

theorem seal_rsa (H : ArithmeticFP) (hR : RSAAssumption) :
    ∃ S : FixedLengthPKScheme, S.msgLen = .var ∧ S.AdaptiveINDSecure .cpa := by
  have hT := (rsaTrapdoor H).shiftParameter_oneWay 2 (rsaTrapdoor_oneWay H hR)
  obtain ⟨_, hE⟩ := TrapdoorCollection.OneWay.exists_glPad_singleBitSecure _
    (rsaTrapdoor_shiftParameter_encD_length H) hT
  obtain ⟨S, hmsg, -, hS⟩ := hE.exists_adaptive_cpa
  exact ⟨S, hmsg, hS⟩

theorem seal_rabin (H : ArithmeticFP) (hD : BlumDensity) (hF : FactoringAssumption) :
    ∃ S : FixedLengthPKScheme, S.msgLen = .var ∧ S.AdaptiveINDSecure .cpa := by
  have hT := (rabinBlumTrapdoor H).shiftParameter_oneWay 3 (rabinBlumTrapdoor_oneWay H hD hF)
  obtain ⟨_, hE⟩ := TrapdoorCollection.OneWay.exists_glPad_singleBitSecure _
    (rabinBlumTrapdoor_shiftParameter_encD_length H) hT
  obtain ⟨S, hmsg, -, hS⟩ := hE.exists_adaptive_cpa
  exact ⟨S, hmsg, hS⟩

-- control: reads `bitwise` through its body; must FAIL sealed
example (S : BitPublicKeyScheme) : S.bitwise.gen = S.gen := rfl

#print axioms TCSlib.Cryptography.Implications.PublicKey.exists_adaptiveCPA_of_rsa
#print axioms TCSlib.Cryptography.Implications.PublicKey.exists_adaptiveCPA_of_factoring
