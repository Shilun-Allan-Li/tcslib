<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/NoiseOperatorExercises.lean :: FABL.abs_noiseOperator_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise Operator Bound on Bounded Functions

**Claim.** If $0\leq\rho\leq1$ and $|f(y)|\leq1$ everywhere, then the noise operator satisfies $|T_\rho f(x)|\leq1$ for every $x$.

**Proof.** The absolute value of the noise operator applied to $f$ is bounded above by the noise operator applied to $|f|$ (\(\texttt{FABL.abs_noiseOperator_le_noiseOperator_abs}\)). At the given point, that operator value is the expectation of $|f|$ under the noise kernel (\(\texttt{FABL.noiseOperator_apply_eq_pmfExpectation}\)). Since $|f(y)|\leq1$ at every point, monotonicity of expectation bounds it by the expectation of the constant function $1$ (\(\texttt{FABL.pmfExpectation_mono}\)). The latter expectation equals $1$ (\(\texttt{FABL.pmfExpectation_const}\)), proving the claim.

**Key facts.** `FABL.abs_noiseOperator_le_noiseOperator_abs`, `FABL.noiseOperator_apply_eq_pmfExpectation`, `FABL.pmfExpectation_mono`, `FABL.pmfExpectation_const`.
