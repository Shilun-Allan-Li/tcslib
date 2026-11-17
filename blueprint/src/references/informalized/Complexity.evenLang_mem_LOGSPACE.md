<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Examples.lean :: Complexity.evenLang_mem_LOGSPACE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even parity is logarithmic-space decidable

**Claim.** The language of Boolean strings with an even number of true bits is decidable in logarithmic space under the stated space measure.

**Proof.** Choose the even-parity scan machine and the constant $c=0$. The machine has no work tapes, so the zero-space theorem says that any function it computes in time is computed using space identically zero (`computesInSpace_zero_of_k_eq_zero`). For each input $x$, the scan machine decides the even-parity language in $|x|+1$ steps (`evenScanTM_decidesInTime`), supplying the required halting computation and output. Its zero space is at most $0\cdot\mathrm{logSpace}(|x|)=0$, so this machine witnesses membership in logarithmic space.

**Key facts.** `Complexity.evenScanTM_decidesInTime`, `Turing.FinTM.computesInSpace_zero_of_k_eq_zero`, `Turing.FinTM.ComputesInSpace.mono`.
