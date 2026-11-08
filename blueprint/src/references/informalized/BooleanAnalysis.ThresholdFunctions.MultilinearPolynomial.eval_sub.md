<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Polynomial.lean :: BooleanAnalysis.ThresholdFunctions.MultilinearPolynomial.eval_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation preserves polynomial differences

**Claim.** For any two multilinear polynomials, evaluating their difference at each point of the cube gives the difference of their evaluations.

**Proof.** Fix an input $x$. Evaluation is a finite sum over subsets, and the coefficient of each character in $F-G$ is $F(S)-G(S)$. Distributing this difference across multiplication by the character and then across the finite sum gives $F.eval(x)-G.eval(x)$. Since this holds at every input, the two functions agree.
