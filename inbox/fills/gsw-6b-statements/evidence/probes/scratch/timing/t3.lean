import TCSlib.Cryptography.LWE.BitEncoding
open TCSlib.Cryptography.LWE TCSlib.Cryptography.LWE.BitEncoding
set_option maxRecDepth 100000
theorem q5 : ∀ v : ZMod (⟨1, 1, 5, by decide⟩ : Parameters).modulus,
    decode ⟨1, 1, 5, by decide⟩ v = true ↔
      decodeLo ⟨1, 1, 5, by decide⟩ ≤ v.val ∧ v.val < decodeHi ⟨1, 1, 5, by decide⟩ := by decide
theorem q63 : ∀ v : ZMod (⟨1, 1, 63, by decide⟩ : Parameters).modulus,
    decode ⟨1, 1, 63, by decide⟩ v = true ↔
      decodeLo ⟨1, 1, 63, by decide⟩ ≤ v.val ∧ v.val < decodeHi ⟨1, 1, 63, by decide⟩ := by decide
#print axioms q63
-- control: a wrong upper end (≤ instead of <) must fail
theorem q63bad : ∀ v : ZMod (⟨1, 1, 63, by decide⟩ : Parameters).modulus,
    decode ⟨1, 1, 63, by decide⟩ v = true ↔
      decodeLo ⟨1, 1, 63, by decide⟩ ≤ v.val ∧ v.val ≤ decodeHi ⟨1, 1, 63, by decide⟩ := by decide
