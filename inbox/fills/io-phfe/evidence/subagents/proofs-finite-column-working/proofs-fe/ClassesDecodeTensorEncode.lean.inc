theorem decodeTensor_encodeTensorBits {p : ℕ+} {l n d : ℕ} (width : ℕ)
    (hwidth : (p : ℕ) ≤ 2 ^ width) (C : PolyTensor p l n d) :
    decodeTensor p l n d width (encodeTensorBits width C) = C := by
  have hparse := Encoding.Modular.decodeMatrix_encodeMatrix width hwidth
    (fun j k => C j ((tupleCoord l d).symm k))
  rw [← encodeTensor_eq, ← ofFn_encodeTensorBits,
    Encoding.Modular.decodeMatrix_eq, Encoding.Modular.decodeVector_eq] at hparse
  split_ifs at hparse
  · simp only [Option.map_some, Option.some.injEq] at hparse
    funext j tau
    simpa only [decodeTensor_eq, decodeResidues_apply, Equiv.symm_apply_apply] using
      congrFun (congrFun hparse j) (tupleCoord l d tau)
  · simp only [Option.map_none, reduceCtorEq] at hparse
