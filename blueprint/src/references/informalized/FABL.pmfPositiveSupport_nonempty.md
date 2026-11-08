<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Reasonableness.lean :: FABL.pmfPositiveSupport_nonempty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonempty Positive Support

**Claim.** For a finite set $\Omega$ and a probability mass function $p$ on it, the set of points $x$ with $p(x)\ne0$ is nonempty.

**Proof.** A probability mass function has nonempty support, so choose a point $x$ in its support. By the definition of support, $p(x)\ne0$. This point belongs to the positive-support finset, since every point belongs to the universe finset and it satisfies the defining nonzero-mass condition.
