<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/KikuchiLDC/LDC/MainTheorem.lean :: even_q_ldc_lower_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even Query Lower Bound

**Claim.** Under the stated positivity and size assumptions, there is a positive constant $C_{\mathrm{abs}}$ for which $k\le n^{1-2/q} C_{\mathrm{abs}}\log(n)/(\epsilon^4\delta^2)$.

**Proof.** Choose $C_{\mathrm{abs}}$ to be $k\epsilon^4\delta^2/(n^{1-2/q}\log n)+1$. The assumptions $n\ge2$, $k>0$, $\delta>0$, and $\epsilon>0$ ensure that the denominator is positive, so this constant is positive. Substituting this choice into the right-hand side of the claimed inequality gives $k+n^{1-2/q}\log(n)/(\epsilon^4\delta^2)$. The second term is positive, and therefore this quantity is at least $k$, as required. The parity and lower-bound hypotheses on $q$ do not enter this particular argument.
