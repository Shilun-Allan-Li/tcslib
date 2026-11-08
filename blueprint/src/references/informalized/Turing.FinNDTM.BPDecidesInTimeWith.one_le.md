<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPTIMEThreshold.lean :: Turing.FinNDTM.BPDecidesInTimeWith.one_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Lower Bound on Halting Time

**Claim.** If the machine satisfies the stated decision condition, then $T(m)\ge 1$ for every natural number $m$.

**Proof.** Fix $n$ and suppose, for contradiction, that $T(n)<1$, so $T(n)=0$. Use the input consisting of $n$ copies of false; its length is $n$. The halting hypothesis at this input, applied to the empty choice word of length zero, says that the initial configuration has halting state. But the initial configuration has state $q_0$, hence its state is nonhalting. This contradiction proves $1\le T(n)$.
