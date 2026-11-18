import TCSlib.Cryptography.SIS.Efficient
attribute [local irreducible] TCSlib.Cryptography.SIS.Parameters.encode TCSlib.Cryptography.SIS.dyadicScheduleParameters TCSlib.Cryptography.SIS.dyadicScheduleFamily TCSlib.Cryptography.SIS.EfficientFamily.ofDyadic TCSlib.Cryptography.SIS.dyadicExample
open TCSlib.Cryptography TCSlib.Cryptography.SIS Complexity Turing
variable (w b : ℕ) (P : SIS.Parameters) (N M W S B : PolyExpr) (hW : ∀ κ, 1 ≤ W.eval κ)
  (hSB : ∀ κ, S.eval κ < 2 ^ B.eval κ) (κ : ℕ)
-- C01 Parameters.encode
example : P.encode w b = pairEncode (List.replicate P.dimension true)
    (pairEncode (List.replicate P.columns true) (pairEncode (Candidates.natToList (w + 1) P.modulus)
      (Candidates.natToList b P.sqNormBound))) := rfl --NEG
example : P.encode w b = pairEncode (List.replicate P.dimension true)
    (pairEncode (List.replicate P.columns true) (pairEncode (Candidates.natToList (w + 1) P.modulus)
      (Candidates.natToList b P.sqNormBound))) := Parameters.encode_eq w b P --POS
-- C02 dyadicScheduleParameters
example : (dyadicScheduleParameters N M W S hW κ).sqNormBound = S.eval κ := rfl --NEG
example : (dyadicScheduleParameters N M W S hW κ).sqNormBound = S.eval κ :=
  dyadicScheduleParameters_sqNormBound N M W S hW κ --POS
-- C03 dyadicScheduleFamily
example : (dyadicScheduleFamily N M W S B hW hSB).magnitudeBits = B := rfl --NEG
example : (dyadicScheduleFamily N M W S B hW hSB).magnitudeBits = B :=
  dyadicScheduleFamily_magnitudeBits N M W S B hW hSB --POS
-- C04 EfficientFamily.ofDyadic
example : (EfficientFamily.ofDyadic N M W S B hW hSB).toFamily = dyadicScheduleFamily N M W S B hW hSB := rfl --NEG
example : (EfficientFamily.ofDyadic N M W S B hW hSB).toFamily = dyadicScheduleFamily N M W S B hW hSB :=
  EfficientFamily.ofDyadic_toFamily N M W S B hW hSB --POS
-- C05 dyadicExample
example : (dyadicExample.parameters κ).sqNormBound = κ + 1 := rfl --NEG
example : (dyadicExample.parameters κ).sqNormBound = κ + 1 := (dyadicExample_parameters κ).2.2.2 --POS
