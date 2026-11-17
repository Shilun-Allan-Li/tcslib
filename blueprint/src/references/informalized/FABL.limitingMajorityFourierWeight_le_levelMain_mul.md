<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierTailAsymptotics.lean :: FABL.limitingMajorityFourierWeight_le_levelMain_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite-dimensional majority level estimate

**Claim.** The supplied Lean declaration proves that for odd $k$, the limiting majority Fourier weight at level $k$ is at most its main approximation multiplied by $1+1/k$.

**Proof.** The given Lean proof uses the upper bound on the error: the difference between the limiting weight and its main approximation is at most the main approximation divided by $k$ (FABL.limitingMajorityFourierWeightError_mem_Icc). Add the main approximation to both sides, then factor it out to obtain the bound by the main approximation times $1+1/k$. The prose in the supplied informal statement describes a different theorem about finite-dimensional majority weights; it is not the claim proved by the formal statement and proof.

**Key facts.** `FABL.limitingMajorityFourierWeightError_mem_Icc`.

**Caveat.** The informal statement does not match the formal declaration; this account follows the formal statement and proof source.
