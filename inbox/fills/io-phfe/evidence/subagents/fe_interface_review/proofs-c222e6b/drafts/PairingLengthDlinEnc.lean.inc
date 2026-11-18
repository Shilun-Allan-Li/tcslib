/-- A reachable public DLIN challenge has one fixed polynomial encoding length.
Serialization glue for [JLS26, §1.1, p. 3].

**Proof sketch.** Use `length_dlinStr`. The shared description's reachability witness supplies
a generator coin string, so `length_desc` fixes the description length. -/
theorem length_dlinEnc (κ : ℕ) (c : G.DLINChallenge κ) :
    (G.dlinEnc κ c).length = 2 * G.descLen.eval κ + 11 * G.wG.eval κ + 12 := by
  obtain ⟨r, hr⟩ := c.pp.description.property
  rw [dlinEnc_eq, length_dlinStr, ← hr, G.length_desc]
