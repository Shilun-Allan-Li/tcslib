<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/KikuchiLDC/LDC/TwoXOR.lean :: two_xor_refutation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Two-XOR Numerical Bound

**Claim.** For the stated positive integers $k,n,d$ with $2\le n$, a positive constant $C_0$ can be chosen so that the displayed upper bound holds for every admissible $n_P$.

**Proof.** Take $C_0=1+n$, which is positive. It suffices to show $\sqrt{n_P}\sqrt{k}\le (1+n)k/\sqrt d$. Since $d>0$, squaring reduces this to $n_Pkd\le (1+n)^2k^2$. The hypothesis $n_Pd\le nk$ gives $n_Pkd\le nk^2$, and $n\le(1+n)^2$ makes the desired inequality follow. Multiplying by the nonnegative factor $n\sqrt{\log n}$ and rearranging yields the claimed bound.
