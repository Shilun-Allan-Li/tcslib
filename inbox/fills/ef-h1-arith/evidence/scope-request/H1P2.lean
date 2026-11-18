import TCSlib.Cryptography.Candidates

/-! H1-P2 consumer smoke test (probe, not library): `ArithmeticFP.ofPrimesInP h` elaborates where
consumers expect `H : ArithmeticFP`. -/

open TCSlib.Cryptography.Candidates

example (h : PrimesInP) (hF : FactoringAssumption) :
    (factoringCollection (ArithmeticFP.ofPrimesInP h)).OneWay :=
  factoringCollection_oneWay (ArithmeticFP.ofPrimesInP h) hF

example (h : PrimesInP) (hR : RSAAssumption) : (rsaCollection (ArithmeticFP.ofPrimesInP h)).OneWay :=
  rsaCollection_oneWay (ArithmeticFP.ofPrimesInP h) hR

example (h : PrimesInP) (G : SafePrimeGen) (hDL : DLAssumption G) :=
  dlCollection_oneWay (ArithmeticFP.ofPrimesInP h) G hDL

example (h : PrimesInP) : Complexity.PolyTimeComputable expEval :=
  polyTimeComputable_expEval (ArithmeticFP.ofPrimesInP h)

example : ArithmeticFP ↔ PrimesInP := arithmeticFP_iff_primesInP

#print axioms ArithmeticFP.ofPrimesInP
#print axioms arithmeticFP_iff_primesInP
#print axioms polyTimeComputable_mulStr
#print axioms polyTimeComputable_addStr
#print axioms polyTimeComputable_subStr
#print axioms polyTimeComputable_divModStr
#print axioms polyTimeComputable_modExpStr
#print axioms polyTimeComputable_leStr
#print axioms polyTimeComputable_sizeStr
#print axioms polyTimeComputable_xgcdStr
#print axioms polyTimeComputable_primeStr_of_primesInP
#print axioms primesInP_of_polyTimeComputable_primeStr
#print axioms primesInP_iff_polyTimeComputable_primeBit
