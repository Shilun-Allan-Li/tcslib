<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.printed_outputPivotal_probability_formula_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Failure of the Pivotal Probability Formula

**Claim.** For the one-dimensional sign cube, the probability that the dictator outputs $-1$ and is pivotal is not the mass of $-1$ multiplied by the dictator's squared $L^2$ distance from its coordinate projection.

**Proof.** The probability of the output-pivotal event is $1/4$ (by the exact computation `biasedOutputPivotalProbability_dictator_one_quarter`). The dictator's product influence, which is the squared distance in the stated formula, is $3/4$ (by `productInfluence_dictator_one_quarter`). The mass assigned to $-1$ at bias $1/4$ is $1/4$. Thus the proposed right-hand side is $(1/4)(3/4)=3/16$, which differs from $1/4$.

**Key facts.** `FABL.biasedOutputPivotalProbability_dictator_one_quarter`, `FABL.productInfluence_dictator_one_quarter`.
