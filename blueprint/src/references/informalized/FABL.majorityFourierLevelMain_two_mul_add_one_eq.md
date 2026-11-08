<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierTailAsymptotics.lean :: FABL.majorityFourierLevelMain_two_mul_add_one_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd-Level Main-Term Identity

**Claim.** For every nonnegative integer $j$, the main Fourier term at level $2j+1$ equals $\frac{2}{\pi(2j+1)}\sqrt{\frac{2}{\pi(2j+1)}}$.

**Proof.** Write $N=2j+1$, which is positive. The factor $(2/\pi)^{3/2}$ can be written as $(2/\pi)\sqrt{2/\pi}$, and the odd-arity power identity gives $N^{-3/2}=1/(N\sqrt N)$ (`FABL.oddArity_rpow_neg_three_halves`). Thus the main term is $(2/\pi)\sqrt{2/\pi}/(N\sqrt N)$. Using positivity of $N$ to combine the square roots, this is $2/(\pi N)\sqrt{2/(\pi N)}$, as claimed.

**Key facts.** `FABL.oddArity_rpow_neg_three_halves`.
