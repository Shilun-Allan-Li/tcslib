<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/NoiseOperatorExercises.lean :: FABL.hypercontractivity_sharp_across_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sharp hypercontractivity across exponents

**Claim.** For $1\le p\le2\le q$, the noise operator with parameter $\sqrt{(p-1)/(q-1)}$ maps the uniform $p$-norm to at most the uniform $q$-norm.

**Proof.** Put $a=\sqrt{p-1}$ and $b=1/\sqrt{q-1}$. The parameter in the claim is $ab$, since the square root of a quotient of nonnegative numbers is the quotient of their square roots. The noise operators compose by multiplying their parameters (`noiseOperator_comp`), so applying first the operator with parameter $a$ and then the one with parameter $b$ gives the operator with parameter $ab$. The two exponent estimates now apply in sequence: the $(2,q)$ estimate bounds the $q$-norm after the second operator by the $2$-norm before it (`twoQHypercontractivity`), and the $(p,2)$ estimate bounds that $2$-norm by the original $p$-norm (`pTwoHypercontractivity`). Combining the inequalities proves the claim.

**Key facts.** `FABL.noiseOperator_comp`, `FABL.twoQHypercontractivity`, `FABL.pTwoHypercontractivity`.
