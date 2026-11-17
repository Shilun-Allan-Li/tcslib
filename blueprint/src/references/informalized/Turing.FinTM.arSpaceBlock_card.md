<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arSpaceBlock_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Block interval cardinality

**Claim.** For every natural number $N$ and integer $z$, the inclusive interval from $(N+1)z$ through $(N+1)z+N+1$ has cardinality $N+2$.

**Proof.** The interval endpoints are $\operatorname{arPos}(N,z,0)=(N+1)z$ and $\operatorname{arPos}(N,z,N+1)=(N+1)z+N+1$. Thus the upper endpoint plus one, minus the lower endpoint, is $N+2$ as an integer. The cardinality formula for an integer closed interval identifies its cardinality with this endpoint difference, converted to a natural number; the result follows.
