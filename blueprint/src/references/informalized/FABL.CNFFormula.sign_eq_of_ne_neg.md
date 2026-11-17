<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.CNFFormula.sign_eq_of_ne_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniqueness of a sign

**Claim.** For signs $x,s\in\{-1,1\}$, if $x\ne -s$, then $x=s$.

**Proof.** Each sign is either $1$ or $-1$. If $s=1$, the assumption excludes $x=-1$, forcing $x=1=s$. If $s=-1$, it excludes $x=1$, forcing $x=-1=s$.
