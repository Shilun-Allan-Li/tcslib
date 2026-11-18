/-- Writing the fixed-width tensor bits gives exactly its canonical word.

**Proof sketch.** The encoder's length is already known. Apply the list reading
round trip at that length; no padding or truncation occurs at any finite index. -/
theorem ofFn_encodeTensorBits {p : ℕ+} {l n d : ℕ} (width : ℕ)
    (C : PolyTensor p l n d) : List.ofFn (encodeTensorBits width C) = encodeTensor width C := by
  simpa only [encodeTensorBits_eq, padFin_def] using
    (ofFn_padFin_of_length (encodeTensor_length width C))
