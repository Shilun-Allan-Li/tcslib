<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: binary_johnson_card_bound_of_admissible -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Johnson bound restated for `AdmissibleCode`

**Claim.** Same conclusion as `binary_johnson_card_bound` — `C.card ≤ 2 * n`
under `0 < n`, `1 ≤ d`, `2 * d ≤ n` and `(w : ℝ) ≤ J2 n d` — but with the two
code hypotheses packaged as the single predicate `AdmissibleCode n d w C`,
which is by definition the conjunction of "pairwise distance at least `d`" and
"all weights at most `w`".

**Proof.** Purely a repackaging: `rcases hC with ⟨hpair, hwt⟩` splits the
definition, then `exact binary_johnson_card_bound hn hd1 hd C hpair hwt hwJ`.

**Used in.** `binary_johnson_bound_radius`, whose `A0_le_of_forall_le` step
hands it a code together with an `AdmissibleCode` witness in exactly this
bundled form.
