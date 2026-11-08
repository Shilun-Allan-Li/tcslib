<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.mean_booleanDual -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of the Boolean dual

**Claim.** For any Boolean function $f$ on the sign cube, the mean of its dual $f^*(x)=-f(-x)$, in real-valued form, is the negative of the mean of $f$.

**Proof.** At each input $x$, the real-valued dual is $-f(x')$ where $x'$ is the coordinatewise negation of $x$. Since coordinatewise negation is a bijection of the sign cube, reindexing the uniform mean by this bijection shows that the mean of $-f(x')$ equals the mean of $-f(x)$. Finally, the mean of a negated function is the negative of its mean. Hence the dual's mean is $-\operatorname{mean}(f)$.
