<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/FiniteFamily.lean :: FABL.finiteFamilyTotalWork_cast_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite-family total work bound

**Claim.** The total work, consisting of the sample count for each member of the family and that count multiplied by the number of coordinates plus one, is at most the stated bound.

**Proof.** Apply the bound on the total number of random examples, which gives $|\mathcal F|N\leq 16|\mathcal F|^3L/\varepsilon^2$. The total-work expression factors as $|\mathcal F|N(n+2)$: its two summands are $|\mathcal F|N$ and $|\mathcal F|N(n+1)$. Since $n+2$ is nonnegative, multiplying the random-example bound by it preserves the inequality. This gives the desired estimate.

**Key facts.** `FABL.finiteFamilyTotalRandomExamples_cast_le`.
