<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/AbelianGroups.lean :: FABL.ComplexFourierSystem.pmfComplexInner_sum_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inner product of a finite linear combination

**Claim.** The probability-weighted inner product of $f$ with the pointwise finite linear combination of the functions $g_i$, with coefficients $a(i)$, is the sum of $a(i)\langle f,g_i\rangle_p$ over $i$.

**Proof.** Expand the inner product and distribute the finite sum over $i$ inside each summand over $x$. Reassociate the factors so that each term is $a(i)$ times the contribution at $x$ from $g_i$. Interchange the two finite sums, then factor $a(i)$ out of the sum over $x$. The resulting inner sum is exactly $\langle f,g_i\rangle_p$, yielding the claimed identity.
