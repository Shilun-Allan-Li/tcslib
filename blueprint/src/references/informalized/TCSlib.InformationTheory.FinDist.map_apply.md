<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/InformationTheory/FinDist.lean :: TCSlib.InformationTheory.FinDist.map_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pushforward Probability

**Claim.** For a map $f\colon\alpha\to\beta$, the distribution induced from $p$ assigns to $b\in\beta$ the sum of $p(a)$ over all inputs $a$ with $f(a)=b$.

**Proof.** This is exactly the probability function used to define the pushforward distribution: at an output $b$, sum the input probabilities over the fiber $\{a:f(a)=b\}$. Unfolding the definition gives the stated formula.
