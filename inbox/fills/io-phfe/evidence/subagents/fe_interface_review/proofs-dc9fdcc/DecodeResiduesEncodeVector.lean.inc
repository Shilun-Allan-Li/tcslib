theorem decodeResidues_encodeVector (p : ℕ+) (count width : ℕ)
    (hwidth : (p : ℕ) ≤ 2 ^ width) (v : Fin count → ZMod (p : ℕ))
    (word : Fin (count * width) → Bool)
    (hword : List.ofFn word = Encoding.Modular.encodeVector width v) :
    decodeResidues p count width word = v := by
  have hparse := Encoding.Modular.decodeVector_encodeVector width hwidth v
  rw [← hword, Encoding.Modular.decodeVector_eq] at hparse
  split_ifs at hparse
  · exact funext fun i => (decodeResidues_apply p count width word i).trans
      (congrFun (Option.some.inj hparse) i)
