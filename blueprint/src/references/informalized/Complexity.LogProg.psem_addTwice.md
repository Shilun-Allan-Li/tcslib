<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem.lean :: Complexity.LogProg.psem_addTwice -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two additions in a probabilistic program

**Claim.** Under the stated instruction pattern, register bounds, and capacity condition, the configuration at the comparison state has the same probabilistic semantics and acceptance probability as the specified configuration at the exit state.

**Proof.** Strengthen the assertion to an arbitrary remaining count $c=v(y)-v(k)$ and induct on $c$. When $c=0$, the compared registers are equal, so execution takes the exit branch; its valuation is the original one, and the equality-branch rule proves the claim. When $c=c_0+1$, they are unequal, so one loop iteration increments $p$ twice and $k$ once. Since $k,p,y$ are pairwise distinct, this leaves $y$ unchanged, raises $p$ by two, and raises $k$ by one. The valuation remains within the bound: the capacity hypothesis bounds the two increments of $p$, and the bound on $y$ bounds the incremented $k$. The remaining difference is $c_0$, so apply the induction hypothesis to this new valuation. Its terminal valuation agrees, register by register, with the one prescribed from the original valuation for $c_0+1$. The three loop increments preserve the probabilistic semantics (`PSem.inc`), and the unequal comparison selects the loop (`PSem.jeq_neg`); the base case uses `PSem.jeq_pos`.

**Key facts.** `Complexity.LogProg.register_update_le`, `Complexity.LogProg.PSem.jeq_pos`, `Complexity.LogProg.PSem.inc`, `Complexity.LogProg.PSem.jeq_neg`.
