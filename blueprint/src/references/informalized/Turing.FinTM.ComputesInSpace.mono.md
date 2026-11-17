<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Basic.lean :: Turing.FinTM.ComputesInSpace.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Space Bounds

**Claim.** If the machine computes each output using space at most $s(|x|)$ and $s(n)\leq s'(n)$ for every $n$, then it computes each output using space at most $s'(|x|)$.

**Proof.** Fix an input $x$. Choose a witnessing time $t$ for the computation under the bound $s$. Its space use is at most $s(|x|)$, which is at most $s'(|x|)$ by the pointwise hypothesis. The same time and computation therefore witness the claim under the larger bound. This works for every input.
