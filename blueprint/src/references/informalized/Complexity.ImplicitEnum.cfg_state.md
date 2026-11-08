<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ImplicitPoly.lean :: Complexity.ImplicitEnum.cfg_state -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# State of an Initial Configuration

**Claim.** For every input word $x$, output word $o$, state $s$, and natural number $i$, the state component of the configuration constructed from them is $s$.

**Proof.** By definition, the configuration is the tuple whose first component is $\operatorname{some}(s)$. Projecting to the state component therefore gives $\operatorname{some}(s)$, as claimed.
