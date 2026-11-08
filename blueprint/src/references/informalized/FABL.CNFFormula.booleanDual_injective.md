<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.CNFFormula.booleanDual_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of Boolean duality

**Claim.** The operation sending a sign-valued Boolean function $f$ to the function $x\mapsto -f(-x)$ is injective.

**Proof.** Suppose two functions have the same Boolean dual. Fix any input $x$ and evaluate that equality at the point $-x$. The resulting equality says that the negatives of the original functions' values at $x$ agree, because negating the input twice returns $x$. Negating both sides then shows the original functions agree at $x$. Since this holds for every input, the functions are equal, proving injectivity.
