<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.signTwistFunctionTester_acceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign-Twisted Tester Acceptance

**Claim.** The sign-twisted tester's acceptance probability on $f$ equals the original tester's acceptance probability on the pointwise product $f\,\mathrm{phase}$.

**Proof.** Expand both acceptance probabilities as averages over the same seed distribution. For each fixed seed, the twisted tester accepts precisely according to the original acceptance predicate applied to the sign-twisted transcript; this follows directly from the definition of the twisted tester. Twisting the transcript of $f$ gives the transcript of the pointwise product $f\,\mathrm{phase}$ (`signTwistTranscript_transcript`). Thus the acceptance indicators agree seed by seed, and therefore their averages are equal.

**Key facts.** `FABL.signTwistTranscript_transcript`.
