<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecValidity_cost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Validity Formula Cost

**Claim.** The validity CNF cost is at most $\bigl(3(|\mathrm{State}(M)|+1)^2+(|\mathrm{State}(M)|+1)+9+21k\bigr)(s+n+2)^2$.

**Proof.** Put $u=s+n+2$ and $q=|\mathrm{State}(M)|+1$. Then $u\ge2$, so $1\le u^2$. Also $n+2\le u$ and $2s+1\le2u$. These inequalities give $(n+2)+1+3(n+2)^2\le5u^2$ and $(2s+1)+1+3(2s+1)^2\le15u^2$. Further, $q+1+3q^2\le(q+1+3q^2)u^2$, while $3(2s+1)\le6u^2$. The raw validity-cost estimate (\texttt{Complexity.codecValidity_cost_raw}) bounds the total by the sum of the input-position contribution, the state contribution, $k$ times the work-position contribution, $k$ times $3(2s+1)$, and $3$. Substituting the preceding bounds and collecting coefficients gives $(3q^2+q+9+21k)u^2$, which is the asserted bound after replacing $q$ and $u$ by their definitions.

**Key facts.** `Complexity.codecValidity_cost_raw`.
