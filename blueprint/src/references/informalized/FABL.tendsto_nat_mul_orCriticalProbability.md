<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.tendsto_nat_mul_orCriticalProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Critical probability scaling limit

**Claim.** As $n\to\infty$, $n(1-\exp(-\log(2)/n))$ tends to $\log 2$.

**Proof.** Put $x_n=\log(2)/n$. Then $x_n\to0$, and $x_n$ is eventually nonzero, so it converges to zero within the punctured real line. The standard exponential limit $(1-e^{-x})/x\to1$ at zero (`tendsto_one_sub_exp_neg_div`) therefore gives $(1-e^{-x_n})/x_n\to1$. Multiplying by $\log 2$ gives convergence to $\log 2$. For each positive $n$, substituting $x_n=\log(2)/n$ identifies this product with the sequence in the claim.

**Key facts.** `FABL.tendsto_one_sub_exp_neg_div`.
