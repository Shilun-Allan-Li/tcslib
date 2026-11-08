<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/KikuchiLDC/LDC/MainTheorem.lean :: main_theorem_ldc_lower_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Existential logarithmic lower bound

**Claim.** Under the stated hypotheses, there exists a positive real constant $C_{\mathrm{abs}}$ such that $k^3\le n C_{\mathrm{abs}}(\log n)^6/(\epsilon^{16}\delta^{16})$.

**Proof.** Choose $C_{\mathrm{abs}}=(k^3\epsilon^{16}\delta^{16}+1)/(n(\log n)^6)$. The hypotheses $k>0$, $n\ge2$, $\epsilon>0$, and $\delta>0$ ensure the numerator and denominator are positive, so $C_{\mathrm{abs}}>0$. Substituting this choice into the claimed right-hand side cancels the factors $n(\log n)^6$ and leaves $k^3+1/(\epsilon^{16}\delta^{16})$. The added term is positive, hence this quantity is at least $k^3$, proving the asserted existence.

**Caveat.** The formal statement proves only existence of a constant that may depend on the parameters. It does not establish the quantitative locally decodable code bound described in the supplied informal discussion.
