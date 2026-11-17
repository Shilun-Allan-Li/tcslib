<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/OneBitHypercontractivity.lean :: FABL.IsHypercontractiveRandomVariable.comp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composition of Hypercontractivity

**Claim.** If $X$ is hypercontractive from exponent $p$ to $r$ with parameter $\sigma$, and from $r$ to $q$ with parameter $\rho$, then it is hypercontractive from $p$ to $q$ with parameter $\rho\sigma$.

**Proof.** Fix real numbers $a,b$. The expression $a+(\rho\sigma)bX$ equals $a+\rho(\sigma b)X$ by associativity and commutativity of real multiplication. Apply the assumed inequality from $r$ to $q$ with inputs $a,\sigma b$, then the assumed inequality from $p$ to $r$ with inputs $a,b$. Transitivity gives the desired bound.
