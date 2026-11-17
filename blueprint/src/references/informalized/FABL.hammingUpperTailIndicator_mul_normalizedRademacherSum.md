<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/HammingBallLimit.lean :: FABL.hammingUpperTailIndicator_mul_normalizedRademacherSum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper-tail indicator identity

**Claim.** The upper-tail indicator multiplied by the normalized Rademacher sum equals the positive part of the sum minus the threshold, plus the threshold times the indicator.

**Proof.** Write \(S\) for the normalized Rademacher sum. If \(S>t\), the indicator is \(1\), and \((S-t)^+=S-t\); hence both sides equal \(S\). If \(S\le t\), the indicator is \(0\), and \((S-t)^+=0\); hence both sides equal \(0\). These two cases prove the identity.
