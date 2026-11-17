<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/FiniteFamily.lean :: FABL.measure_finiteFamily_someCoefficientBadSetWithParameters_le_one_tenth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-tenth coefficient union bound

**Claim.** With confidence parameter chosen as $1/(10|\mathcal F|)$, the probability that any coefficient estimate in a nonempty finite family falls in its bad set is at most $1/10$.

**Proof.** The finite-family union estimate (`FABL.measure_finiteFamily_someCoefficientBadSetWithParameters_le`) bounds the probability by $|\mathcal F|$ times the chosen confidence parameter. Here that parameter is $1/(10|\mathcal F|)$, so the product is $1/10$.

**Key facts.** `FABL.measure_finiteFamily_someCoefficientBadSetWithParameters_le`.
