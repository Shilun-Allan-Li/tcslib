<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.oddWeightShortProofPCPPSystem_acceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance After Appending True

**Claim.** For every Boolean input word $w$ of length $m+2$ and proof word $q$ of length $m$, the short-proof system's acceptance probability on $(w,q)$ equals the partial-sum system's acceptance probability on $(w,q')$, where $q'$ appends a final true bit to $q$.

**Proof.** Both acceptance probabilities are expectations over the same seed distribution, since the short-proof verifier inherits that distribution from the partial-sum verifier. It is therefore enough to compare their acceptance indicators seed by seed. For each seed, restoring the value at any query to the omitted final proof position as true makes the short-proof transcript equal to the partial-sum transcript on the proof extended by a true bit (\texttt{oddWeightShortProofPCPPSystem\_transcript}). The short verifier applies the partial-sum acceptance rule to precisely this restored transcript. Thus the two acceptance decisions agree for every seed, and taking their common-distribution expectations proves the equality.

**Key facts.** `FABL.oddWeightShortProofPCPPSystem_transcript`.
