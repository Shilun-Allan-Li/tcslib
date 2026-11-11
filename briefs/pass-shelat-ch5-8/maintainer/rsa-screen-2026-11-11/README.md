# RSA / Rabin catalog screen (2026-11-11)

Campaign head `3f921e63d` (after #291). A probe (`Compose.lean`, log `compose.log`) composes only
published theorems; it compiles (rc 0) and both witnesses print `[propext, Classical.choice, Quot.sound]`.

**RSA** (`ArithmeticFP`, `RSAAssumption`):
`rsaTrapdoor_oneWay` → `TrapdoorCollection.shiftParameter_oneWay _ 2` → `TrapdoorCollection.OneWay.exists_glPad_singleBitSecure`
with `m = 2(n+2)` and `henc := rsaTrapdoor_shiftParameter_encD_length` (from #284) → `SingleBitSecure.exists_adaptive_cpa`
(#287, #290, #291) ⇒ `∃ S : FixedLengthPKScheme, S.msgLen = .var ∧ S.AdaptiveINDSecure .cpa`.

**Rabin** (`ArithmeticFP`, `BlumDensity`, `FactoringAssumption`): the same route at `n+3` with
`rabinBlumTrapdoor_oneWay` and `rabinBlumTrapdoor_shiftParameter_encD_length`.

No new proof obligations remain: the catalog entries are short compositions. The witness record
`FixedLengthPKScheme` carries uniform efficient key generation and encryption, polynomial-time
decryption, fixed ciphertext width and perfect correctness. The probe needs the import of
`Encryption.PublicKey.Trapdoor` in addition to `BitwiseCPA`, `Candidates.RSA`, `Candidates.Rabin`.
