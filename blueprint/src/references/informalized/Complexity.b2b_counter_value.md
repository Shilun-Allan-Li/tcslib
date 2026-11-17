<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.b2b_counter_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Value of All Ones

**Claim.** For every natural number $Q$, the base-two value of the length-$Q$ digit string consisting entirely of ones is $2^Q-1$.

**Proof.** Proceed by induction on $Q$. For $Q=0$, the digit list is empty, whose value is $0=2^0-1$. For the successor step, the list of $Q+1$ ones consists of a leading one followed by $Q$ ones. The base-two digit recurrence therefore gives its value as $1+2$ times the value of the length-$Q$ list. By the induction hypothesis this is $1+2(2^Q-1)=2^{Q+1}-1$.
