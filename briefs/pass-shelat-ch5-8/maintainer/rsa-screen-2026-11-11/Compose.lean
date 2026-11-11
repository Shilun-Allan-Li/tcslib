import TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA
import TCSlib.Cryptography.Encryption.PublicKey.Trapdoor
import TCSlib.Cryptography.Candidates.RSA
import TCSlib.Cryptography.Candidates.Rabin

open TCSlib.Cryptography TCSlib.Cryptography.Composability TCSlib.Cryptography.Candidates Complexity

theorem probe_rsa (H : ArithmeticFP) (hR : RSAAssumption) :
    ∃ S : FixedLengthPKScheme, S.msgLen = .var ∧ S.AdaptiveINDSecure .cpa := by
  have hT := (rsaTrapdoor H).shiftParameter_oneWay 2 (rsaTrapdoor_oneWay H hR)
  obtain ⟨E, hE⟩ := TrapdoorCollection.OneWay.exists_glPad_singleBitSecure _ (rsaTrapdoor_shiftParameter_encD_length H) hT
  obtain ⟨S, h1, -, h3⟩ := hE.exists_adaptive_cpa
  exact ⟨S, h1, h3⟩

theorem probe_rabin (H : ArithmeticFP) (hD : BlumDensity) (hF : FactoringAssumption) :
    ∃ S : FixedLengthPKScheme, S.msgLen = .var ∧ S.AdaptiveINDSecure .cpa := by
  have hT := (rabinBlumTrapdoor H).shiftParameter_oneWay 3 (rabinBlumTrapdoor_oneWay H hD hF)
  obtain ⟨E, hE⟩ := TrapdoorCollection.OneWay.exists_glPad_singleBitSecure _ (rabinBlumTrapdoor_shiftParameter_encD_length H) hT
  obtain ⟨S, h1, -, h3⟩ := hE.exists_adaptive_cpa
  exact ⟨S, h1, h3⟩

#print axioms probe_rsa
#print axioms probe_rabin
