<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Fingerprint.lean :: Randomized.AlgCircuit.zeroTest_of_toMvPolynomial_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Test on the Zero Polynomial

**Claim.** If an algebraic circuit has associated polynomial zero over the integers, then its zero test returns true on every Boolean string.

**Proof.** The zero test returns true precisely when every tested evaluation in the corresponding residue ring is zero. Fix any trial. The evaluation of the circuit in that residue ring is the evaluation of its associated polynomial under the same input assignment (`aeval_toMvPolynomial`). By hypothesis the associated polynomial is zero, and a ring homomorphism sends zero to zero. Thus this trial evaluates to zero; since the trial was arbitrary, the zero-test condition holds.

**Key facts.** `Randomized.AlgCircuit.aeval_toMvPolynomial`.
