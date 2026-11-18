
/-! ### The fields (with the every-input equations of `Arithmetic.lean`) -/

/-- **Binary multiplication is polynomial-time** (the field `ArithmeticFP.mul`):
`PolyTimeComputable mulStr`, from `polyTimeComputable_mulStr_pairEncode` and `mulStr_eq`. -/
theorem polyTimeComputable_mulStr : PolyTimeComputable mulStr :=
  polyTimeComputable_mulStr_pairEncode.congr fun z => by rw [mulStr_pairEncode, mulStr_eq]

/-- **Binary addition is polynomial-time** (the field `ArithmeticFP.add`):
`PolyTimeComputable addStr`. -/
theorem polyTimeComputable_addStr : PolyTimeComputable addStr :=
  polyTimeComputable_addStr_pairEncode.congr fun z => by rw [addStr_pairEncode, addStr_eq]

/-- **Truncated subtraction is polynomial-time** (the field `ArithmeticFP.sub`):
`PolyTimeComputable subStr`. -/
theorem polyTimeComputable_subStr : PolyTimeComputable subStr :=
  polyTimeComputable_subStr_pairEncode.congr fun z => by rw [subStr_pairEncode, subStr_eq]

/-- **Division with remainder is polynomial-time** (the field `ArithmeticFP.divMod`):
`PolyTimeComputable divModStr`. -/
theorem polyTimeComputable_divModStr : PolyTimeComputable divModStr :=
  polyTimeComputable_divModStr_pairEncode.congr fun z => by
    rw [divModStr_pairEncode, divModStr_eq]

/-- **Modular exponentiation is polynomial-time** (the field `ArithmeticFP.modExp`)
[PS10, Algorithm 45.5, Theorem 45.6]: `PolyTimeComputable modExpStr`. -/
theorem polyTimeComputable_modExpStr : PolyTimeComputable modExpStr :=
  polyTimeComputable_modExpStr_pairEncode.congr fun z => by
    rw [modExpStr_pairEncode, modExpStr_eq]

/-- **Comparison is polynomial-time** (the field `ArithmeticFP.le`):
`PolyTimeComputable leStr`. -/
theorem polyTimeComputable_leStr : PolyTimeComputable leStr :=
  polyTimeComputable_leStr_pairEncode.congr fun z => by rw [leStr_pairEncode, leStr_eq]
