<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DeterministicGoldreichLevin.lean :: FABL.DeterministicGoldreichLevinInput.restrictedWeightInput_epsilon -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restricted weight accuracy

**Claim.** The restricted weight input has accuracy $\tau^2/8$.

**Proof.** The restricted weight input is built from a bias whose numerator is $a^2$ and whose denominator is $8(4Ma d)^2$, where $M$ is the family-size bound and $d$ is the original accuracy denominator. Its accuracy is therefore $a^2/[8(4Mad)^2]$. The threshold is the rational number $(a/d)/(4M)=a/(4Md)$, so its square divided by eight is the same expression. The definition of the learning parameter supplies $a/d$, and the threshold construction supplies this displayed rational quotient; simplifying the fractions proves the identity. Positivity of the family-size bound ensures the denominators are nonzero (`familySizeBound_pos`).

**Key facts.** `FABL.DeterministicGoldreichLevinInput.familySizeBound_pos`.
