<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.DepthCircuit.initialRestrictionWidth_le_step_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restriction-width step bound

**Claim.** For every nonnegative integer $s$, if $L(s)=\lceil\log_2(s+1)\rceil$, then $5L(s)+14\leq20(L(s+1)+2)$.

**Proof.** Write $q(s)=L(s)+2$, the logarithmic quantity used in the width definitions. Since $s+1\leq s+2$, monotonicity of the ceiling base-$2$ logarithm gives $q(s)\leq q(s+1)$. Also $q(s+1)\geq1$. Therefore $5q(s)+4\leq5q(s+1)+4\leq20q(s+1)$, where the last inequality follows from $4\leq15q(s+1)$. Substituting $q(s)=L(s)+2$ yields the stated bound.
