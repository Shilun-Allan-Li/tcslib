<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterSplit_loop_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Elementary Loop Bound

**Claim.** For natural numbers $c,A,n,t$, $c\bigl(A(t+n+2)+1\bigr)(n+2)\le 2c(A+1)(n+1)(t+n+2)$.

**Proof.** Since $t+n+2\ge 1$, expand the right-hand factor to see $A(t+n+2)+1\le (A+1)(t+n+2)$. Also $n+2\le 2(n+1)$. Multiplying these inequalities by the nonnegative factors and rearranging the products gives the stated bound.
