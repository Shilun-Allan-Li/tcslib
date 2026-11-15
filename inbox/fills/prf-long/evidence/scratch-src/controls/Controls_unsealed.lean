import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF

/-! Paired Rule-10 seal controls of the prf-long fill. Each `CONTROL` example reads a foreign
definition by `rfl` (a negative: it must close unsealed and fail exactly once sealed); each
`READER` example proves the same fact through the published reader (it must close sealed); the
`PROBE` records how the projection-coercion instance behaves under the two seal variants. The
line `-- (no seal)` is replaced by the seal harness of the variant. -/

-- (no seal)

open Complexity Turing TCSlib.Cryptography

-- CONTROL C1 (MultiMsg.histBlockOut, a ReductionMachine definition)
example (p : (Fin 2 → Bool) × (Fin 3 → Bool)) :
    MultiMsg.histBlockOut p = pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) [] := rfl
-- READER C1
example (p : (Fin 2 → Bool) × (Fin 3 → Bool)) :
    MultiMsg.histBlockOut p = pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) [] :=
  MultiMsg.histBlockOut_eq p

-- CONTROL C2 (prfEncRealOut, a Hybrid definition)
example (F : Bool → (Fin 2 → Bool) → (Fin 3 → Bool)) (m : Fin 2 → Fin 3 → Bool)
    (z : Bool × (Fin 2 → Fin 2 → Bool)) (j : Fin 2) :
    prfEncRealOut F m z j = (z.2 j, m j + F z.1 (z.2 j)) := rfl
-- READER C2
example (F : Bool → (Fin 2 → Bool) → (Fin 3 → Bool)) (m : Fin 2 → Fin 3 → Bool)
    (z : Bool × (Fin 2 → Fin 2 → Bool)) (j : Fin 2) :
    prfEncRealOut F m z j = (z.2 j, m j + F z.1 (z.2 j)) := prfEncRealOut_apply F m z j

-- CONTROL C3 (encodeTupleOut, a MultiMsgOut definition)
example (v : Fin 2 → (Fin 2 → Bool) × (Fin 3 → Bool)) :
    encodeTupleOut v = PrivateKeyScheme.encodeList
      (List.ofFn fun j => pairEncode (List.ofFn (v j).1) (List.ofFn (v j).2)) := rfl
-- READER C3
example (v : Fin 2 → (Fin 2 → Bool) × (Fin 3 → Bool)) :
    encodeTupleOut v = PrivateKeyScheme.encodeList
      (List.ofFn fun j => pairEncode (List.ofFn (v j).1) (List.ofFn (v j).2)) :=
  encodeTupleOut_eq v

-- CONTROL C4 (MultiMsg.maskOfOut, a ReductionMachine definition)
example (v : Fin 2 → Fin 3 → Bool) :
    MultiMsg.maskOfOut 2 v = (List.ofFn fun j => MultiMsg.maskBlockOut 2 (v j)).flatten := rfl
-- READER C4
example (v : Fin 2 → Fin 3 → Bool) :
    MultiMsg.maskOfOut 2 v = (List.ofFn fun j => MultiMsg.maskBlockOut 2 (v j)).flatten :=
  MultiMsg.maskOfOut_eq 2 v

-- CONTROL C5 (PolyExpr.eval: closes when it is notation, fails when it is sealed)
example (ℓ t : PolyExpr) (n : ℕ) : (PolyExpr.add ℓ t).eval n = ℓ.eval n + t.eval n := rfl
-- READER C5
example (ℓ t : PolyExpr) (n : ℕ) : (PolyExpr.add ℓ t).eval n = ℓ.eval n + t.eval n :=
  PolyExpr.eval_add ℓ t n

-- PROBE C6 (FinDist's projection coercion, read through its instance: the only request in which
-- the strict and coe variants differ; recorded, not a control)
example {α : Type} [Fintype α] (d : TCSlib.InformationTheory.FinDist α) (a : α) :
    (TCSlib.InformationTheory.FinDist.instCoeFunForallReal (α := α)).coe d a = d.prob a := rfl

-- CONTROL C7 (encodeHist, an Asymptotic/Defs definition; `encodeHist_eq_flatMapOut` reads it
-- through `encodeHist_nil`/`encodeHist_cons`)
example (p : (Fin 2 → Bool) × (Fin 3 → Bool)) (h : List ((Fin 2 → Bool) × (Fin 3 → Bool))) :
    encodeHist (p :: h) = pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) (encodeHist h) :=
  rfl
-- READER C7
example (p : (Fin 2 → Bool) × (Fin 3 → Bool)) (h : List ((Fin 2 → Bool) × (Fin 3 → Bool))) :
    encodeHist (p :: h) = pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) (encodeHist h) :=
  encodeHist_cons p h
