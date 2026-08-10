<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: A0_le_of_forall_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A uniform bound on admissible codes bounds `A0`

**Claim.** If every `C : Finset (BitVec n)` satisfying `AdmissibleCode n d w C`
has `C.card ≤ K`, then `A0 n d w ≤ K`. Here `A0 n d w` is defined as the
supremum of `Finset.card` over the admissible members of
`(Finset.univ).powerset`.

**Proof.** One line: `Finset.sup_le fun C hC => by aesop`. `Finset.sup_le`
reduces the supremum bound to a per-element bound, and `aesop` strips the
`Finset.mem_filter` / `mem_powerset` membership hypothesis down to
`AdmissibleCode n d w C` and feeds it to `h`.

**Used in.** `binary_johnson_bound_radius` — this is the only bridge from the
per-code statement to the extremal quantity `A0`.
