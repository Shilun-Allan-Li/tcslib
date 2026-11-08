<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.isLocalTester_signTwist -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Local testing is preserved by sign twists

**Claim.** Twisting a nonadaptive tester’s answers by a fixed sign function preserves its local testing rate for the correspondingly twisted property.

**Proof.** The rate remains positive because it is unchanged. If $f$ satisfies the twisted property, then its twist satisfies the original property; the tester’s acceptance probability on $f$ equals the original tester’s acceptance probability on that twist (\texttt{signTwistFunctionTester\_acceptanceProbability}). Perfect completeness therefore follows from that of the original tester.

For soundness, fix a function $f$ that is far from every function satisfying the twisted property. Apply the original tester’s soundness guarantee to the twisted input. If $g$ satisfies the original property, then twisting $g$ again gives a function satisfying the twisted property, because twisting is involutive (\texttt{signTwist\_involutive}). The assumed distance condition on $f$ therefore applies to that twice-twisted function. Twisting both functions preserves relative Hamming distance (\texttt{relativeHammingDist\_signTwist}); involutivity then shows that the twisted input is at least as far from every original-property function as required. The original soundness bound applies, and the tester’s rejection probability identity transfers that bound to the twisted tester.

**Key facts.** `FABL.signTwistFunctionTester_acceptanceProbability`, `FABL.signTwist_involutive`, `FABL.relativeHammingDist_signTwist`.
