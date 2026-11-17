<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.tautDual_segment_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composition of Anchor-Free Run Segments

**Claim.** If a run of $a$ steps takes $c$ to $d$ without an anchor-state visit before its endpoint, and a run of $b$ steps takes $d$ to $e$ with the same property, then the run of $a+b$ steps takes $c$ to $e$ and has no anchor-state visit before its endpoint.

**Proof.** The run-after-addition law says that running $a+b$ steps from $c$ is the same as running $b$ steps from the configuration reached after $a$ steps (`Turing.MultiTapeTM.runFrom_add`). The two endpoint equalities therefore concatenate to show that this run reaches $e$. For any time $j<a+b$, if $j<a$, the first segment’s anchor-avoidance condition applies directly. Otherwise write $j=a+(j-a)$; the inequality $j<a+b$ gives $j-a<b$. The run at time $j$ is then the second segment’s run at time $j-a$, so its anchor-avoidance condition applies as well.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`.
