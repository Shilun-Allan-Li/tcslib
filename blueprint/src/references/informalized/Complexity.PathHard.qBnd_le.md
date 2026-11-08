<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardDecide.lean :: Complexity.PathHard.qBnd_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Bound on the Query Bound

**Claim.** With the code-width parameter $K$, define $e=K(c_0+1)$, $D=2^{K+2}2^e$, and $q=(|y|+1)^e$. Then the query bound is at most $(8D^2+9)(|y|+1)^{2e+1}$, which is the displayed polynomial bound.

**Proof.** The estimate on the exponential vertex bound gives $nV(K,c_0,|y|)\le Dq$ (Complexity.PathHard.nV_le). Since $q\ge1$, squaring yields $nV^2\le(Dq)^2$, and the length term satisfies $|y|\le q^2(|y|+1)$. Also $(Dq)^2\le D^2q^2(|y|+1)$ because $|y|+1\ge1$. Finally, $(|y|+1)^{2e+1}=q^2(|y|+1)$. Substituting these bounds into $|y|+8nV^2+8$ and collecting terms gives at most $(8D^2+9)q^2(|y|+1)$, as required.

**Key facts.** `Complexity.PathHard.nV_le`.
