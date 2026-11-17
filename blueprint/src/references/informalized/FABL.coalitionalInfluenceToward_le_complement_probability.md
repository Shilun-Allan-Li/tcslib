<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.coalitionalInfluenceToward_le_complement_probability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence and Complementary Output Probability

**Claim.** The coalitional influence toward $b$ is at most one minus the probability that the function equals $b$.

**Proof.** By definition, influence is the coalition success probability minus the probability that the function already equals $b$. The success probability is at most $1$ (`uniformProbability_le_one`). Subtracting the same probability from both sides yields the claimed inequality.

**Key facts.** `FABL.uniformProbability_le_one`.
