<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.oddWeightShortProofPCPPSystem_rejectionProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rejection Probability Preservation

**Claim.** For every Boolean input word $w$ of length $m+2$ and proof word $p$ of length $m$, the short-proof verifier's rejection probability equals that of the partial-sum verifier on the proof obtained by appending a final true bit to $p$.

**Proof.** Rejection probability is one minus acceptance probability. Substitute this definition for each verifier's rejection probability, then apply the equality of acceptance probabilities under appending a true proof bit (\texttt{oddWeightShortProofPCPPSystem\_acceptanceProbability}). The resulting expressions are equal, proving the claim.

**Key facts.** `FABL.oddWeightShortProofPCPPSystem_acceptanceProbability`.
