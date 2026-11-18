
/-! ### The bridge and the bundle (with the readers of `PRIMESBin` and `PRIMES`) -/

/-- Glue. The little-endian primality test is the indicator of `PRIMESBin`:
`[bitsVal x is prime] = [x ∈ PRIMESBin]` (`Randomized.mem_PRIMESBin`, `Randomized.mem_PRIMES`,
`MultiTapeTM.indicator_eq_true_iff`). -/
theorem primeBit_eq_indicator (x : List Bool) :
    decide (LogProg.bitsVal x).Prime = MultiTapeTM.indicator Randomized.PRIMESBin x := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, MultiTapeTM.indicator_eq_true_iff,
    Randomized.mem_PRIMESBin, Randomized.mem_PRIMES]

/-- **`PRIMES ∈ P` is the polynomial-time little-endian test**: `PrimesInP` holds if and only if
`x ↦ [bitsVal x is prime]` is polynomial-time (`test_of_mem_P`, `mem_P_of_test`). -/
theorem primesInP_iff_polyTimeComputable_primeBit :
    PrimesInP ↔ PolyTimeComputable fun x => [decide (LogProg.bitsVal x).Prime] := by
  rw [primesInP_iff]
  constructor
  · intro h
    exact (test_of_mem_P h).congr fun x => by rw [primeBit_eq_indicator]
  · intro h
    have hP := mem_P_of_test h
    have hset : {z : List Bool | decide (LogProg.bitsVal z).Prime = true} =
        Randomized.PRIMESBin := by
      ext x
      rw [Set.mem_setOf_eq, decide_eq_true_iff, Randomized.mem_PRIMESBin, Randomized.mem_PRIMES]
    rwa [hset] at hP

/-- **`PRIMES ∈ P` gives the bundle's primality field**: `PrimesInP → PolyTimeComputable primeStr`
[PS10, §2.6.5] (glue through `toLE`, `test_of_mem_P`). -/
theorem polyTimeComputable_primeStr_of_primesInP (h : PrimesInP) : PolyTimeComputable primeStr :=
  polyTimeComputable_primeStr_iff_bitsVal.2 (primesInP_iff_polyTimeComputable_primeBit.1 h)

/-- **The bundle's primality field gives `PRIMES ∈ P`**:
`PolyTimeComputable primeStr → PrimesInP` (glue through `fromLEPoly`, `mem_P_of_test`). -/
theorem primesInP_of_polyTimeComputable_primeStr (h : PolyTimeComputable primeStr) :
    PrimesInP :=
  primesInP_iff_polyTimeComputable_primeBit.2 (polyTimeComputable_primeStr_iff_bitsVal.1 h)

/-- **The arithmetic bundle from `PRIMES ∈ P`**: `PrimesInP → ArithmeticFP`. The eight
arithmetic fields are proved unconditionally (`ArithmeticDischarge.lean`,
`ExtendedEuclidMachine.lean`); only primality uses the hypothesis. -/
theorem ArithmeticFP.ofPrimesInP (h : PrimesInP) : ArithmeticFP where
  mul := polyTimeComputable_mulStr
  add := polyTimeComputable_addStr
  sub := polyTimeComputable_subStr
  divMod := polyTimeComputable_divModStr
  xgcd := polyTimeComputable_xgcdStr
  modExp := polyTimeComputable_modExpStr
  le := polyTimeComputable_leStr
  size := polyTimeComputable_sizeStr
  prime := polyTimeComputable_primeStr_of_primesInP h

/-- **The arithmetic bundle is exactly `PRIMES ∈ P`**: `ArithmeticFP ↔ PrimesInP`. -/
theorem arithmeticFP_iff_primesInP : ArithmeticFP ↔ PrimesInP :=
  ⟨fun H => primesInP_of_polyTimeComputable_primeStr H.prime, ArithmeticFP.ofPrimesInP⟩
