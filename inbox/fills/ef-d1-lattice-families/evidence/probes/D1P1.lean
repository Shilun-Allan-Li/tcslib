import TCSlib.Cryptography.LWE.Efficient
import TCSlib.Cryptography.SIS.Efficient
/-! D1-P1 probe (evidence only, outside the library): the instances elaborate, and the parameter
words at κ ≤ 3 agree with the encoding. -/
open TCSlib.Cryptography Turing

#check (LWE.dyadicExample : LWE.EfficientFamily)
#check (SIS.dyadicExample : SIS.EfficientFamily)

def bits (l : List Bool) : String := String.mk (l.map fun b => if b then '1' else '0')

-- LWE: the parameter word (n, m, q) and its expected form ⟨1^{κ+1}, ⟨1^{2(κ+1)²}, 1 0^{κ+1}⟩⟩
#eval (List.range 4).map fun κ =>
  (κ, (LWE.dyadicExample.parameters κ).dimension, (LWE.dyadicExample.parameters κ).samples,
    (LWE.dyadicExample.parameters κ).modulus, LWE.dyadicExample.residueBits.eval κ,
    bits ((LWE.dyadicExample.parameters κ).encode (LWE.dyadicExample.residueBits.eval κ)))
#eval (List.range 4).map fun κ =>
  (LWE.dyadicExample.parameters κ).encode (LWE.dyadicExample.residueBits.eval κ) ==
    pairEncode (List.replicate (κ + 1) true) (pairEncode (List.replicate (2 * (κ + 1) ^ 2) true)
      (true :: List.replicate (κ + 1) false))
-- LWE noise word: seedModulusWord 0 = [true] (numeral of 1), noiseWord samples
#eval (List.range 4).map fun κ => bits (LWE.dyadicExample.noiseInput κ)
#eval [(-3 : ℤ), -1, 0, 1, 2, 5].map fun e => (e, bits (LWE.noiseWord e))
-- centeredCore on ⟨1^κ, r⟩ with T = 1 (2 seed bits): value = r0 - r1
#eval [[false, false], [true, false], [false, true], [true, true]].map fun r =>
  (bits r, bits (LWE.centeredCore (.const 1) (pairEncode (List.replicate 3 true) r)))
-- SIS: the parameter word (n, m, q, β) and its expected form
#eval (List.range 4).map fun κ =>
  (κ, bits ((SIS.dyadicExample.parameters κ).encode (SIS.dyadicExample.residueBits.eval κ)
    (SIS.dyadicExample.magnitudeBits.eval κ)))
#eval (List.range 4).map fun κ =>
  (SIS.dyadicExample.parameters κ).encode (SIS.dyadicExample.residueBits.eval κ)
      (SIS.dyadicExample.magnitudeBits.eval κ) ==
    pairEncode (List.replicate (κ + 1) true) (pairEncode (List.replicate (2 * (κ + 1) ^ 2) true)
      (pairEncode (true :: List.replicate (κ + 1) false) (Candidates.natToList (κ + 1) (κ + 1))))
-- kernel checks (decide), κ = 0..3
example : ∀ κ < 4, (LWE.dyadicExample.parameters κ).encode (LWE.dyadicExample.residueBits.eval κ) =
    pairEncode (List.replicate (κ + 1) true) (pairEncode (List.replicate (2 * (κ + 1) ^ 2) true)
      (true :: List.replicate (κ + 1) false)) := by decide
