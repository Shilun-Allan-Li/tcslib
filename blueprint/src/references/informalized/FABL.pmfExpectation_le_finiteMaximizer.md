<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPAlgorithms.lean :: FABL.pmfExpectation_le_finiteMaximizer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation Bounded by a Maximum

**Claim.** On a finite nonempty set, the expectation of a real-valued function under a probability mass function is at most its value at a maximizing point.

**Proof.** Every value $f(x)$ is at most the value at the chosen maximizer (\texttt{FABL.le\_finiteMaximizer}). Monotonicity of expectation therefore bounds the expectation of $f$ by the expectation of the constant function with value $f(\mathrm{finiteMaximizer}(f))$ (\texttt{FABL.pmfExpectation\_mono}). That constant has expectation equal to itself (\texttt{FABL.pmfExpectation\_const}), giving the desired bound.

**Key facts.** `FABL.le_finiteMaximizer`, `FABL.pmfExpectation_mono`, `FABL.pmfExpectation_const`.
