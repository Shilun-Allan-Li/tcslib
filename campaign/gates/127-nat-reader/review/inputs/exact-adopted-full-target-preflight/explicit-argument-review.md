# Full target argument review

| Full target step | Classification |
|---|---|
| `rw [← foldr_bit_eq_ofDigits]` | Existing imported theorem; proof value is a citation boundary. |
| First `change Nat.bit true ((canonCount ...).foldr Nat.bit 0) = _` | Exposes own canonOffset and core list computation. It passes with all3 foreign/focused heads opaque, including incFixed beneath the own canonCount definition. |
| `(canonCount_spec ...).2.2` and `.2.1` | Same-owner private theorem projections. Their type/value footprint is inspected. Their earlier legacy proof bodies are outside this one-target sealing claim. |
| `rw [← codeBitsNat_eq]` | Exact repaired foreign conversion: public CodeParser theorem, line132, rewriting foldr to the named decoder. Foreign codeBitsNat is not unfolded by change. |
| `rw [codeBitsNat_bits]` | Existing imported CodeParser theorem. |
| `simp only [Nat.bit_val, Bool.toNat_true]` | Existing public Mathlib/Core equations; retained Nat.bit repair. |
| `length_bits_le_self` | Existing imported theorem. |
| `simp only [canonOffset, List.length_cons, ...]` | Own definition plus Core list theorem and the same-owner width projection. No imported ordinary definition is explicitly listed. |

The only ordinary foreign TCS heads reached through the target and same-owner
helper types/values are codeBitsNat and incFixed; Nat.bit is the additional
focused Mathlib guard. All3 are guarded before the complete target doc/header/
body. Imported theorem proof values remain boundaries; other Mathlib/Core
internals and earlier same-owner helper proof bodies are not claimed sealed.
No remaining explicit foreign-definition argument appears in the target.
