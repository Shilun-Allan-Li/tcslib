/-- Fixed-width group encodings make the tuple length depend only on the description length
and group width. This is serialization glue for [JLS26, §1.1, p. 3].

**Proof sketch.** Apply `length_pairEncode` to the six nested pairs and `List.length_ofFn`
to each group encoding; collect the coefficients of the fixed width. -/
theorem length_dlinStr {wG wT : ℕ} (B : BilinearGroup wG wT) (d : List Bool)
    (g a b u v w : B.G) :
    (dlinStr B d g a b u v w).length = 2 * d.length + 11 * wG + 12 := by
  simp only [dlinStr_eq, length_pairEncode, List.length_ofFn]
  omega
