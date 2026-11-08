<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.sat_pt_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Equality Test

**Claim.** If $f$ is polynomial-time computable and $w$ is a fixed binary word, then the function returning the one-bit word recording whether $f(x)=w$ is polynomial-time computable.

**Proof.** A fixed-word equality test is computable in linear time: on input $y$, return $[\mathrm{true}]$ if $y=w$ and $[\mathrm{false}]$ otherwise (`Turing.FinTM.computesFunInTime_ifEq`), hence it is polynomial-time computable (`Complexity.sat_pt_linear`). Compose this test with the given polynomial-time computation of $f$ (`Complexity.PolyTimeComputable.comp`). The resulting function returns exactly the one-bit truth value of $f(x)=w$.

**Key facts.** `Turing.FinTM.computesFunInTime_ifEq`, `Complexity.sat_pt_linear`, `Complexity.PolyTimeComputable.comp`.
