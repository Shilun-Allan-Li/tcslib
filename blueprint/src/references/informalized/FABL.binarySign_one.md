<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/VectorFourier.lean :: FABL.binarySign_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Sign of One

**Claim.** The binary sign of $1\in\mathbb{F}_2$ is $-1$.

**Proof.** Represent the binary sign as the sign-value map applied to the sign encoding (`FABL.signValue_signEncode_eq_binarySign`). The sign encoding of $1$ is $-1$ (`FABL.signEncode_one`), and the sign value of $-1$ is $-1$ (`FABL.signValue_neg_one`). Combining these identities gives the result.

**Key facts.** `FABL.signValue_signEncode_eq_binarySign`, `FABL.signEncode_one`, `FABL.signValue_neg_one`.
