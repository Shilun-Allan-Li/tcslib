<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterInstr.lean :: Complexity.UTab.prev_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewriting a Natural-Number Equation

**Claim.** If $t\ne0$ and $q+S=tS+a$, then $q=(t-1)S+a$.

**Proof.** Since $t$ is a nonzero natural number, write it as $t'+1$, where $t'=t-1$. The given equation becomes $q+S=(t'+1)S+a=t'S+S+a$. Cancel the common summand $S$ from both sides to obtain $q=t'S+a$. Since $t'=t-1$, this is the desired identity.
