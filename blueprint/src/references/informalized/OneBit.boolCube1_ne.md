<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/OneBit.lean :: boolCube1_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The two points of the one-bit cube are distinct

**Claim.** `(fun _ : Fin 1 => false) ≠ (fun _ : Fin 1 => true)`, i.e. the two
elements of `BoolCube 1` listed by `boolCube1_univ` are different points.
A `private` enumeration helper.

**Proof.** Immediate from `decide` — both sides are decidable functions on the
finite type `Fin 1`. ∎

**Used in.** The distinctness side condition of `Finset.sum_pair` when a sum over
`BoolCube 1` is written out as two terms, e.g. in `expect_abs_rpow_one_bit`.
