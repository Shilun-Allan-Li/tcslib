<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.arm_chain -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Increment and Decrement Chains

**Claim.** Under the stated instruction and value bounds, a chain of $k$ increments or decrements reaches the prescribed final state with the selected register increased by $k$ or decreased by $k$, respectively, and all intermediate configurations satisfy the side conditions and the bound $B$.

**Proof.** We argue by induction on the chain length $k$, allowing the label sequence and initial register values to vary. For $k=0$, the final register update leaves every value unchanged, and the initial configuration itself witnesses reachability by reflexivity of reachability ($\texttt{AReach.refl}$). Suppose the result holds for chains of length $k$, and consider one of length $k+1$. The instruction at $\ell_0$ is the required increment or decrement, so one step moves to $\ell_1$ and changes only register $r$, giving it the value $v(r)+1$ or $v(r)-1$. Call the resulting valuation $v'$. The assumed bound on $v(r)+k+1$ in the increment case, or on $k+1$ relative to $v(r)$ in the decrement case, together with the original bounds, ensures every coordinate of $v'$ is at most $B$. The first configuration also satisfies the side conditions: the current instruction is an increment or decrement, for which those conditions hold. Apply the induction hypothesis to the shifted label sequence $i\mapsto\ell_{i+1}$ and valuation $v'$. Its numerical side condition follows from the original one after accounting for the first step. The induction hypothesis reaches label $\ell_{k+1}$ with the remaining $k$ changes. Combining the first step with this reachability gives reachability for the full chain ($\texttt{AReach.step}$). Updating register $r$ twice is the same as updating it once by the total increment or decrement, so the resulting valuation is exactly the one claimed.

**Key facts.** `Complexity.LogProg.AReach.refl`, `Complexity.LogProg.AReach.step`.
