<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/General.lean :: BooleanAnalysis.Hypercontractivity.coarse_radius_le_sharp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coarse radius bounded by the sharp radius

**Claim.** For $q>2$ and $0<\lambda<1$, the coarse radius $\lambda^{1/2-1/q}/\sqrt{q-1}$ is at most the sharp discrete radius at parameter $\lambda/(1+\lambda)$.

**Proof.** Set $u=\log(1/\lambda)>0$. Since $q>2$, the two positive arguments $a=u/q$ and $b=u/(q/(q-1))$ satisfy $a\le b$, and direct simplification gives $a/b=1/(q-1)$. The hyperbolic-sine ratio bound (\texttt{sinh\_ratio\_lower\_bound}) gives $(a/b)e^{a-b}\le\sinh(a)/\sinh(b)$. Using $u=-\log\lambda$, one computes $a-b=\log(\lambda)(1-2/q)$, so $e^{a-b}=\lambda^{1-2/q}$. The sharp-radius parameter simplifies as $(1-\lambda/(1+\lambda))/(\lambda/(1+\lambda))=1/\lambda$, hence its defining hyperbolic-sine ratio is precisely $\sinh(a)/\sinh(b)$. Finally, both radii are nonnegative; squaring the desired inequality reduces it to the preceding ratio bound, using $(q-1)>0$ and $(1/2-1/q)2=1-2/q$. Taking square roots yields the claim.

**Key facts.** `BooleanAnalysis.Hypercontractivity.sinh_ratio_lower_bound`.
