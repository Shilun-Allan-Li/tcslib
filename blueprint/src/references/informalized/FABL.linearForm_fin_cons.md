<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/FKN.lean :: FABL.linearForm_fin_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear Form on a Prefixed Vector

**Claim.** For a coefficient vector of length $n+1$, the linear form evaluated at the vector obtained by prefixing a sign $b$ to $x$ equals the contribution $a_0b$ from the first coordinate plus the linear form from the remaining coordinates.

**Proof.** Expand the defining sum over the $n+1$ coordinates into its first term and the sum over the remaining $n$ coordinates. The prefixed vector has value $b$ at the first coordinate and agrees with $x$ after shifting the index, so these terms are exactly $a_0\,\mathrm{signValue}(b)$ and the linear form with coefficients $a_i$ for $i=1,\ldots,n$.
