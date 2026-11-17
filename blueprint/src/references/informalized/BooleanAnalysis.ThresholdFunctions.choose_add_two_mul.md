<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Majority.lean :: BooleanAnalysis.ThresholdFunctions.choose_add_two_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-Step Binomial Identity

**Claim.** If $N=k+a$ for natural numbers $N,k,a$, then $\binom{N+2}{k}(a+2)(a+1)=\binom Nk(N+2)(N+1)$.

**Proof.** Substitute $N=k+a$. The successive binomial recurrence `Nat.choose_mul_succ_eq` gives $(k+a+1)\binom{k+a+2}{k}=(a+2)\binom{k+a+1}{k}$ and $(k+a)\binom{k+a+1}{k}=(a+1)\binom{k+a}{k}$, after simplifying the natural-number differences in the recurrence. Multiplying these identities and rearranging the factors yields the claimed equality.
