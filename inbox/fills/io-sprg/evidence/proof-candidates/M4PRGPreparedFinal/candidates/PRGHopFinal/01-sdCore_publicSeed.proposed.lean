/-- The packed core publishes its instance vectors and its actual error bit; glue.
[JLS26, SdSamp′, pp. 15-16]. This theorem compares the deterministic vector maps.

**Proof sketch.** Read the core fields, public packing equation, and publicSeed
coordinate equation. Both sides then have the same explicit sum-coordinate match. -/
theorem Params.sdCore_publicSeed (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I : P.Idx' κ pp) (d : P.Draw κ pp) :
    (P.sdCore κ pp I d).seed.1 =
      P.publicSeed κ pp (fun k => ((P.sdCore κ pp I d).instances k).pub)
        (P.sdCore κ pp I d).err := by
  rw [P.sdCore_seed, P.publicSeed_eq, P.sdCore_instances, P.sdCore_err,
    P.packSeed_fst]
