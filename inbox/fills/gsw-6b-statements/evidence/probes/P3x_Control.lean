import TCSlib.Cryptography.LWE.BitEncoding
/-! Probe P3x (negative control for P3): the interval with a wrong upper end (`≤ decodeHi`) or a
wrong lower end (`decodeLo - 1 ≤`) must be refuted by `decide` at q = 63 and q = 8; expected:
exactly 4 errors "decide proved that the proposition ... is false". -/
open TCSlib.Cryptography.LWE TCSlib.Cryptography.LWE.BitEncoding
abbrev LP (q : ℕ) (h : 2 ≤ q) : Parameters := ⟨1, 1, q, h⟩
theorem bad_hi_63 : ∀ v : ZMod (LP 63 (by decide)).modulus, decode (LP 63 (by decide)) v = true ↔
    decodeLo (LP 63 (by decide)) ≤ v.val ∧ v.val ≤ decodeHi (LP 63 (by decide)) := by decide
theorem bad_lo_63 : ∀ v : ZMod (LP 63 (by decide)).modulus, decode (LP 63 (by decide)) v = true ↔
    decodeLo (LP 63 (by decide)) - 1 ≤ v.val ∧ v.val < decodeHi (LP 63 (by decide)) := by decide
theorem bad_hi_8 : ∀ v : ZMod (LP 8 (by decide)).modulus, decode (LP 8 (by decide)) v = true ↔
    decodeLo (LP 8 (by decide)) ≤ v.val ∧ v.val ≤ decodeHi (LP 8 (by decide)) := by decide
theorem bad_lo_8 : ∀ v : ZMod (LP 8 (by decide)).modulus, decode (LP 8 (by decide)) v = true ↔
    decodeLo (LP 8 (by decide)) - 1 ≤ v.val ∧ v.val < decodeHi (LP 8 (by decide)) := by decide
