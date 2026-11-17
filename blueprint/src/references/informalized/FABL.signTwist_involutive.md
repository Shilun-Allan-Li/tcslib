<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.signTwist_involutive -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Involution of sign twisting

**Claim.** For maps $\phi,f:\Omega\to\{\pm1\}$, twisting $f$ pointwise by $\phi$ twice returns $f$.

**Proof.** Evaluate both sides at an arbitrary $x\in\Omega$. The value $\phi(x)$ is either $1$ or $-1$. In either case, multiplying $f(x)$ by $\phi(x)$ twice leaves $f(x)$ unchanged, since each of these two signs squares to $1$. Hence the functions agree at every input.
