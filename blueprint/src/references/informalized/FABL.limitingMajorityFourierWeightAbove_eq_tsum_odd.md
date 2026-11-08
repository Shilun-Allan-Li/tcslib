<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierTailAsymptotics.lean :: FABL.limitingMajorityFourierWeightAbove_eq_tsum_odd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd-level Fourier weight tail formula

**Claim.** When $k$ is odd, the limiting majority Fourier weight above $k$ equals $\sum_{r=0}^{\infty} w_{k+2(r+1)}$.

**Proof.** First express the tail over all indices above $k$ as the shifted sum $\sum_{r=0}^{\infty}w_{k+1+r}$ (`FABL.limitingMajorityFourierWeightAbove_eq_shifted_tsum`). For odd $k$, the shifted-sum identity states that this sum equals the sum over indices $k+2(r+1)$ (`FABL.shifted_limitingMajorityFourierWeight_tsum_eq_odd`). Combining the equalities proves the formula.

**Key facts.** `FABL.limitingMajorityFourierWeightAbove_eq_shifted_tsum`, `FABL.shifted_limitingMajorityFourierWeight_tsum_eq_odd`.
