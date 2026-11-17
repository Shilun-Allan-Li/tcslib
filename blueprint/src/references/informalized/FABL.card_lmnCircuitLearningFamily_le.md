<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.card_lmnCircuitLearningFamily_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low-Degree Fourier Family Bound

**Claim.** The family of subsets of the $n$-element coordinate set whose sizes are at most the prescribed circuit-learning degree $D$ has cardinality at most $(D+1)(n+1)^D$.

**Proof.** Apply the general low-degree Fourier family bound (`FABL.card_lowDegreeFourierFamily_le`) with $k=D$, where $D$ is the prescribed circuit-learning degree. That bound gives cardinality at most $(D+1)(n+1)^D$, as claimed.

**Key facts.** `FABL.card_lowDegreeFourierFamily_le`.
