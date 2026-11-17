<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/NP.lean :: Complexity.pairedVerifier_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time closure of the paired verifier

**Claim.** If $V$ is decidable in polynomial time, then the paired verifier language defined by $C$, $c$, and $V$ is also decidable in polynomial time.

**Proof.** Build a polynomial-time indicator for the paired verifier by combining polynomial-time checks. First, parse the input and form the concatenation of the decoded components; parsing validity and pair concatenation are computable in linear time, and the indicator of $V$ is polynomial-time by the hypothesis. Composing these procedures gives a polynomial-time test for whether the concatenation lies in $V$. Next, use polynomial-time tests for the upper and reverse length bounds to require that the payload length equals $C(|x|+1)^c$: when both bounds hold, antisymmetry gives equality, and when either fails the test rejects. Finally, include the polynomial-time parser-validity check, making each failed check select the constant false output. For an unparsable string the resulting indicator is false; for a parsed pair it is true exactly when the payload has the required length and the concatenation belongs to $V$. Thus this is a polynomial-time indicator of the paired verifier language, and the polynomial-time indicator characterization of membership in $P$ (`verifier_mem_P`) yields the result.

**Key facts.** `Complexity.polyTimeComputable_const`, `Turing.FinTM.computesFunInTime_pairConcat`, `Complexity.polyTimeComputable_of_linear`, `Complexity.verifier_poly_indicator`, `Complexity.PolyTimeComputable.comp`, `Complexity.verifier_poly_reverseBound`, `Complexity.polyTimeComputable_ite`, `Complexity.verifier_poly_bound`, `Turing.FinTM.computesFunInTime_pairValid`, `Complexity.verifier_mem_P`.
