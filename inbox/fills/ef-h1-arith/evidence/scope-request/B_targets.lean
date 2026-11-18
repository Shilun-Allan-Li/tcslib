
/-- **The extended Euclidean algorithm is polynomial-time** (the field `ArithmeticFP.xgcd`)
[PS10, Algorithm 43.2, Claim 43.3]: `PolyTimeComputable xgcdStr`, from
`polyTimeComputable_xgcdStr_pairEncode` and `xgcdStr_eq`. -/
theorem polyTimeComputable_xgcdStr : PolyTimeComputable xgcdStr :=
  polyTimeComputable_xgcdStr_pairEncode.congr fun z => by rw [xgcdStr_pairEncode, xgcdStr_eq]
