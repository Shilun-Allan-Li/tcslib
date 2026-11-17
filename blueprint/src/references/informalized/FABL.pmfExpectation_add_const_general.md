<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.pmfExpectation_add_const_general -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation of a Constant Shift

**Claim.** For a probability mass function on a finite set, adding a constant $c$ to a real-valued function adds $c$ to its expectation.

**Proof.** View the constant shift as the pointwise sum of $f$ and the constant function with value $c$. By additivity of expectation (\texttt{FABL.pmfExpectation\_add\_fun}), its expectation is the sum of the expectations of these two functions. The expectation of a constant function under a probability mass function is that constant (\texttt{FABL.pmfExpectation\_const}), so the result is $\mathbb E_\pi f+c$.

**Key facts.** `FABL.pmfExpectation_add_fun`, `FABL.pmfExpectation_const`.
