<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaResources.lean :: FABL.lowDegreeJuntaDyadicFailure_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dyadic Failure Parameter Value

**Claim.** For every natural number $b$, the rational value of the dyadic failure parameter with $b$ confidence bits is $2^{-(b+1)}$.

**Proof.** The parameter is defined as the subtype consisting of the rational number $1/2^{b+1}$ together with a proof that it lies in the required interval. Its value is therefore exactly that rational number, by the definition of the subtype constructor.
