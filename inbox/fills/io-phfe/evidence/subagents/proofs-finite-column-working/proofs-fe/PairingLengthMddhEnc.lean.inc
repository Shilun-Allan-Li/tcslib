/-- The matrix-challenge word has a fixed polynomial length. Serialization glue.

**Proof sketch.** Use the shared public encoding reader, `length_pairEncode`,
`length_groupMatrixEnc`, and `length_desc` from the description's reachability witness. -/
theorem length_mddhEnc (d ℓ : PolyExpr) (κ : ℕ) (c : G.MDDHChallenge d ℓ κ) :
    (G.mddhEnc d ℓ κ c).length =
      4 * G.descLen.eval κ + (2 + 4 * ℓ.eval κ + ℓ.eval κ * d.eval κ) * G.wG.eval κ + 8 :=
  by
    obtain ⟨r, hr⟩ := c.pp.description.property
    simp only [mddhEnc_eq, PublicParams.encode_eq, length_pairEncode,
      BilinearGroup.length_groupMatrixEnc, List.length_ofFn]
    rw [← hr, G.length_desc]
    ring
