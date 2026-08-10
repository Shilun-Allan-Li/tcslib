<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: BitVec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# `BitVec n`: binary words of length `n`

**Definition.** `BitVec n` is the abbreviation `Fin n → Bool`: a word of `n`
bits, indexed by `Fin n`. Codes in this file are finite sets of such words
(`Finset (BitVec n)`), and the basic quantities `wt` (number of `true`
coordinates), `hdist` (number of disagreeing coordinates) and `pmOne`
(the `±1` embedding into `Euc n`) are all defined on it.

**Remark.** This is an `abbrev` inside `namespace CodingTheory.Johnson`, so it is
reducible and definitionally transparent — `simp`/`decide` see through it to
`Fin n → Bool`, and instances such as `DecidableEq` and `Fintype` are inherited
from the function type. It is namespace-local and distinct from Lean core's
`BitVec` (the packed bitvector type), which plays no role here.
