<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/Siegenthaler.lean :: FABL.not_odd_scaled_eq_finer_scaled -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd Scaling Cannot Match a Finer Scale

**Claim.** If $z$ is an odd integer and $k<d$, then $z/2^d\ne w/2^k$ for any integer $w$.

**Proof.** Assume the scaled quantities are equal and clear the nonzero denominators. This gives $z2^k=w2^d$ as a real equality, and hence as an integer equality. Since $d>k$, write $d=k+(d-k)$ and factor out $2^k$ to obtain $2^kz=2^k(w2^{d-k})$. Cancellation gives $z=w2^{d-k}$. Here $d-k>0$, so $2^{d-k}$ is even; consequently its product with $w$ is even, forcing $z$ to be even. This contradicts the assumption that $z$ is odd.
