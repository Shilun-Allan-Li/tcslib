<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/UniformNoiseStability.lean :: FABL.noiseSensitivity_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unit Bound for Noise Sensitivity

**Claim.** For every Boolean function and every noise rate $0\le\delta\le1$, its noise sensitivity is at most $1$.

**Proof.** Noise sensitivity is the expectation of the indicator that the function takes different values on the two correlated inputs. Pointwise, this indicator is at most the constant function $1$, so its expectation is at most the expectation of $1$. The expectation of a constant-one function under any probability distribution is $1$ (\texttt{pmfExpectation_const_one}), proving the bound.

**Key facts.** `FABL.pmfExpectation_const_one`.
