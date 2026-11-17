<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/ExtremalBounds.lean :: FABL.hammingNorm_firstCoordinateSlices -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hamming norm of coordinate slices

**Claim.** For every $n\ge 0$ and function $f:\mathbb F_2^{n+1}\to\mathbb F_2$, its Hamming norm is the sum of the Hamming norms of its two first-coordinate slices, at $0$ and $1$.

**Proof.** First express each Hamming norm as the size of the corresponding one-support (\texttt{hammingNorm\_eq\_card\_f₂OneSupport}); equivalently, it is the sum over inputs of the indicator that the function equals $1$. Reindex the inputs of length $n+1$ by pairs $(b,x)$, where $b\in\mathbb F_2$ is the first coordinate and $x\in\mathbb F_2^n$ is the remaining tail. The sum over all inputs becomes the sum first over $b$ and then over $x$. Since $\mathbb F_2=\{0,1\}$, the two terms in the outer sum are precisely the indicators defining the one-supports of the two slices. Their sums are the respective slice norms, giving the identity.

**Key facts.** `FABL.hammingNorm_eq_card_f₂OneSupport`.
