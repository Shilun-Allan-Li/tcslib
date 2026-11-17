<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codec_size_normalize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial size bound

**Claim.** For natural numbers $A,C,t$ with $C\ge1$ and $t\ge1$, one has $\bigl(A(t+1)^2+2Ct\bigr)(Ct+3)+1\le(3A+7)C^2(t+1)^3$.

**Proof.** First, $t\le(t+1)^2$. Also $A\le AC$ because $C\ge1$. Multiplying these inequalities by the appropriate nonnegative factors and collecting terms gives $A(t+1)^2+2Ct\le(A+2)C(t+1)^2$. Separately, $Ct+3\le3C(t+1)$, using $C,t\ge1$. Thus the product on the left is at most $(A+2)C(t+1)^2\cdot3C(t+1)$. Finally, $1\le C^2(t+1)^3$; adding this to the product bound yields an upper bound of $3(A+2)C^2(t+1)^3+C^2(t+1)^3$, which is exactly $(3A+7)C^2(t+1)^3$.
