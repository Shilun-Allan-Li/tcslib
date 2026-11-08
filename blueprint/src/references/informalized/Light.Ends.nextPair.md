<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/NextPair.lean :: Light.Ends.nextPair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution of a Counter Update

**Claim.** Under the stated arithmetic, word-limit, initial-frame, and index-distinctness hypotheses, the counter update executes within cost $T$ and ends in a state satisfying $Q$ at the prescribed updated frame.

**Proof.** Write $a=t/n$ and $b=t\bmod n$. The initial locals $A,B,N$ therefore contain $a,b,n$. The proof first executes the assignment $B:=b+1$ using `Light.Ends.setToThen`; its expression is safe and its cost fits the available budget by the word-limit assumptions and $14\le T$.

Now split on whether the updated value $b+1$ equals $n$. The condition is safe, and its evaluation cost fits the remaining budget, so the conditional execution principle (`Light.Ends.iteLast`) applies.

If $b+1=n$, the natural-number division and remainder identities for the wraparound case (`Nat.succ_div_mod_of_eq`) give $(t+1)/n=a+1$ and $(t+1)\bmod n=0$. Execute the true branch: set $B:=0$, then set $A:=a+1$. The two assignments are justified by `Light.Ends.setTo` and `Light.Ends.setToThen`; the index inequality $A\ne B$ ensures that resetting $B$ does not alter the value used for the update to $A$. The resulting frame is the prescribed frame, so the assumed postcondition $Q$ holds.

If $b+1\ne n$, the non-wraparound division and remainder identities (`Nat.succ_div_mod_of_ne`) give $(t+1)/n=a$ and $(t+1)\bmod n=b+1$. The false branch is `skip`, justified by `Light.Ends.skip`. Here $B\ne N$ ensures that updating $B$ does not change the value at $N$ used to select the branch, and the frame after the update agrees with the prescribed frame. In both cases the same memory is retained, and the cost estimates for the initial assignment, condition, and selected branch fit within $T$.

**Key facts.** `Light.Ends.setToThen`, `Light.Ends.iteLast`, `Nat.succ_div_mod_of_eq`, `Light.Ends.setTo`, `Light.Ends.setToThen`, `Nat.succ_div_mod_of_ne`, `Light.Ends.skip`.
