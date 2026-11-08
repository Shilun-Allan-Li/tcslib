<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathLoops.lean :: Complexity.LogProg.psem_addOnce -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Single addition in a probabilistic program

**Claim.** Under the stated instruction pattern, register bounds, and capacity condition, the configuration at the comparison state has the same probabilistic semantics and acceptance probability as the specified configuration at the exit state.

**Proof.** Generalize the assertion to a remaining increment count $c=v(y)-v(j)$ and induct on $c$. If $c=0$, the compared registers are equal, so the program takes the exit branch directly; the exit valuation is the original valuation, and the equality-branch rule gives the result. If $c=c_0+1$, the registers are unequal and the program takes the loop branch. One loop iteration increments $R$ and then $j$. Because the three registers are distinct, these changes leave $y$ unchanged and increase $R$ by one and $j$ by one. The updated valuation remains bounded: the capacity hypothesis bounds the new value of $R$, and the old bound on $y$ bounds the incremented value of $j$. The remaining difference is $c_0$. Apply the induction hypothesis to this updated valuation; the terminal valuation it specifies agrees, register by register, with the terminal valuation specified from the original valuation for count $c_0+1$. Each loop increment preserves the probability semantics (`PSem.inc`), and the unequal-register comparison selects that loop (`PSem.jeq_neg`). The equality branch in the base case uses `PSem.jeq_pos`.

**Key facts.** `Complexity.LogProg.register_update_le`, `Complexity.LogProg.PSem.jeq_pos`, `Complexity.LogProg.PSem.inc`, `Complexity.LogProg.PSem.jeq_neg`.
