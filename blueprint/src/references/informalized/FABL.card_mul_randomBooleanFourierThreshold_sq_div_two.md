<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RandomBooleanFourierMaximum.lean :: FABL.card_mul_randomBooleanFourierThreshold_sq_div_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean Fourier Threshold Identity

**Claim.** For every natural number $n$, the Boolean cube has cardinality $2^n$, and multiplying this by the square of $\tau_n=2\sqrt{n}\,2^{-n/2}$ and dividing by $2$ gives $2n$.

**Proof.** The cube has $2^n$ points, since each of its $n$ coordinates has two possible signs. Also $(\sqrt n)^2=n$, and the square of $2^{-n/2}$ is $2^{-n}=(2^n)^{-1}$. Substituting these into the left-hand side gives $2^n\cdot 4n\cdot(2^n)^{-1}/2=2n$.
