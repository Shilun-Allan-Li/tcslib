<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPoly.lean :: Randomized.PolyAmp.runVal_two_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper Bound for the Run Value

**Claim.** Let $N$ be a finite-state nondeterministic Turing machine over Boolean symbols and let $x$ be a Boolean input. For any nonnegative integer $K$, if the probability that $N$ accepts on a uniformly random choice word of length $K$ is at most $1/3$, then the run value with the rejecting decision rule, $K$ blocks, initial count $0$, and parameter $i=K+1$ is at most $2(8/9)^{\lfloor(K+1)/2\rfloor}$.

**Proof.** The rejecting decision rule declares success only when the number of accepting blocks is large enough that $K+1<2m$ fails; equivalently, success implies $K+1\le 2m$. Thus the event counted by the run value is contained in the event that at least half of the $K+1$ blocks accept. By monotonicity of uniform probability under event inclusion (`Randomized.randProb_mono`), the run value is at most the probability of this latter event. The block tail bound says that if the acceptance probability of one block is at most $1/2-\varepsilon$, then the probability that at least half of $K+1$ independent blocks accept is at most $2(1-4\varepsilon^2)^{\lfloor(K+1)/2\rfloor}$ (`Randomized.randProb_tail_le`). Taking $\varepsilon=1/6$ is permitted by the hypothesis $1/3=1/2-1/6$, and $1-4(1/6)^2=8/9$. Substitution gives the claimed bound.

**Key facts.** `Randomized.randProb_tail_le`, `Randomized.randProb_mono`.
