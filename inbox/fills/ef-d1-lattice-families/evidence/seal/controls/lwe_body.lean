open TCSlib.Cryptography TCSlib.Cryptography.LWE Complexity Turing
variable (w : ℕ) (P : LWE.Parameters) (e : ℤ) (n : ℕ) (r : Fin n → Bool) (l : List Bool)
  (N M W T : PolyExpr) (hW : ∀ κ, 1 ≤ W.eval κ) (χ : ℕ → Noise) (κ : ℕ) (F : LWE.Family)
  (t : PolyExpr) (nn : ℕ → ℕ) (hn : ∀ κ, nn κ = t.eval κ) (hs : CenteredSampleEq T)
-- C01 Parameters.encode
example : P.encode w = pairEncode (List.replicate P.dimension true)
    (pairEncode (List.replicate P.samples true) (Candidates.natToList (w + 1) P.modulus)) := rfl --NEG
example : P.encode w = pairEncode (List.replicate P.dimension true)
    (pairEncode (List.replicate P.samples true) (Candidates.natToList (w + 1) P.modulus)) :=
  Parameters.encode_eq w P --POS
-- C02 noiseWord
example : noiseWord e = decide (e < 0) :: Nat.bits e.natAbs := rfl --NEG
example : noiseWord e = decide (e < 0) :: Nat.bits e.natAbs := noiseWord_eq e --POS
-- C03 seedModulusWord
example : seedModulusWord n = Candidates.natToList (n + 1) (2 ^ n) := rfl --NEG
example : seedModulusWord n = Candidates.natToList (n + 1) (2 ^ n) := seedModulusWord_eq n --POS
-- C04 seedWord
example : seedWord r = false :: List.ofFn r := rfl --NEG
example : seedWord r = false :: List.ofFn r := seedWord_eq r --POS
-- C06 onesCount
example : onesCount l = pairFstD (BinArith.countLoop (Randomized.onesW l)) := rfl --NEG
example : onesCount l = Nat.bits (l.count true) := onesCount_eq l --POS
-- C07 signedDiff
example : signedDiff l = if BinArith.le (pairEncode (pairSndD l) (pairFstD l)) then
    false :: BinArith.sub l else true :: BinArith.sub (pairEncode (pairSndD l) (pairFstD l)) := rfl --NEG
example : signedDiff l = if BinArith.le (pairEncode (pairSndD l) (pairFstD l)) then
    false :: BinArith.sub l else true :: BinArith.sub (pairEncode (pairSndD l) (pairFstD l)) :=
  signedDiff_eq l --POS
-- C08 centeredCore
example : centeredCore T l = signedDiff (pairEncode
    (onesCount ((pairSndD l).take (T.eval (pairFstD l).length)))
    (onesCount ((pairSndD l).drop (T.eval (pairFstD l).length)))) := rfl --NEG
example : centeredCore T l = signedDiff (pairEncode
    (onesCount ((pairSndD l).take (T.eval (pairFstD l).length)))
    (onesCount ((pairSndD l).drop (T.eval (pairFstD l).length)))) := centeredCore_eq T l --POS
-- C09 dyadicParameters
example : (dyadicParameters N M W hW κ).dimension = N.eval κ := rfl --NEG
example : (dyadicParameters N M W hW κ).dimension = N.eval κ := dyadicParameters_dimension N M W hW κ --POS
-- C10 dyadicFamily
example : (dyadicFamily N M W hW χ).noise = χ := rfl --NEG
example : (dyadicFamily N M W hW χ).noise = χ := dyadicFamily_noise N M W hW χ --POS
-- C11 Family.boundedModulus
example : ((F.boundedModulus κ).1 : ℕ) = (F.parameters κ).modulus := rfl --NEG
example : ((F.boundedModulus κ).1 : ℕ) = (F.parameters κ).modulus := Family.boundedModulus_val F κ --POS
-- C12 seedModulus
example : ((seedModulus t nn hn κ).1 : ℕ) = 2 ^ nn κ := rfl --NEG
example : ((seedModulus t nn hn κ).1 : ℕ) = 2 ^ nn κ := seedModulus_val t nn hn κ --POS
-- C13 CenteredSampleEq
example : CenteredSampleEq T ↔ ∀ κ (c : (centeredNoise (T.eval κ)).Coins),
    (centeredNoise (T.eval κ)).sample c =
      centeredValue (T.eval κ) (cast (centeredNoise_Coins (T.eval κ)) c) := Iff.rfl --NEG
example : CenteredSampleEq T ↔ ∀ κ (c : (centeredNoise (T.eval κ)).Coins),
    (centeredNoise (T.eval κ)).sample c =
      centeredValue (T.eval κ) (cast (centeredNoise_Coins (T.eval κ)) c) := centeredSampleEq_iff T --POS
-- C14 EfficientFamily.ofDyadic (and ofBitSeeds beneath it)
example : (EfficientFamily.ofDyadic N M W T hW hs).toFamily =
    dyadicFamily N M W hW fun κ => centeredNoise (T.eval κ) := rfl --NEG
example : (EfficientFamily.ofDyadic N M W T hW hs).toFamily =
    dyadicFamily N M W hW fun κ => centeredNoise (T.eval κ) := EfficientFamily.ofDyadic_toFamily N M W T hW hs --POS
-- C15 dyadicExample
example : dyadicExample.noise κ = centeredNoise 0 := rfl --NEG
example : dyadicExample.noise κ = centeredNoise 0 := dyadicExample_noise κ --POS
