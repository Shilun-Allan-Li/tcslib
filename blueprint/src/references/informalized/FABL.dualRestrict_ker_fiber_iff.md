<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/SparseSpectrum.lean :: FABL.dualRestrict_ker_fiber_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fibers of restriction from a hyperplane kernel

**Claim.** For nonzero $\beta$, the restrictions of $\psi$ and $\gamma$ to $\ker\beta$ agree exactly when $\psi=\gamma$ or $\psi=\gamma+\beta$.

**Proof.** If the restrictions agree, their difference $\psi-\gamma$ vanishes on $\ker\beta$. The kernel of restriction to $\ker\beta$ is the one-dimensional span of $\beta$ (\texttt{FABL.ker_dualRestrict_ker_eq_span}), so $\psi-\gamma=c\beta$ for some $c\in\mathbb F_2$. Since $\mathbb F_2$ has only the scalars $0$ and $1$, if $c=0$ then $\psi=\gamma$, while if $c=1$ then $\psi=\gamma+\beta$; here subtraction equals addition in characteristic two. Conversely, if either equality holds, the restrictions agree: in the second case $\beta$ vanishes on its kernel, so adding it does not change the restriction.

**Key facts.** `FABL.ker_dualRestrict_ker_eq_span`.
