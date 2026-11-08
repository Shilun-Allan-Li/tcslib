<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PolyTimeModel.lean :: Randomized.sipser_gacs_polyTime -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time BPP in the Second Level

**Claim.** Every language with a polynomial-time randomized verifier using polynomially many random bits and error at most $1/3$ belongs to both $\Sigma_2^P$ and $\Pi_2^P$.

**Proof.** For the polynomial-time verifier model, the closure results provide closure under majority, answer negation, and shift-or. The BPP-to-second-level theorem therefore gives membership in the model's existential second-level class and in its universal counterpart. The characterization theorem identifies existential second-level membership in this model with $\Sigma_2^P$. Apply that characterization to the language itself for the first conclusion, and to its complement for the second; by definition, the latter is equivalent to membership in $\Pi_2^P$.

**Key facts.** `Randomized.polyTimeModel_closedUnderMajority`, `Randomized.polyTimeModel_closedUnderNot`, `Randomized.polyTimeModel_closedUnderShiftOr`, `Randomized.sipser_gacs`, `Randomized.inSigma2_polyTimeModel_iff`, `Randomized.inSigma2_polyTimeModel_iff`.
