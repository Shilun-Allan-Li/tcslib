<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_syntax_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Scanner Transition

**Claim.** For every scanner state $q$, bit $b$, and binary word $x$, scanning $b$ followed by $x$ from $q$ gives the same acceptance bit as scanning $x$ from the state reached by one transition on $b$.

**Proof.** The scanner processes a list by folding its transition function from left to right. Thus the first bit $b$ updates state $q$ to the state reached by that transition, and the remaining fold processes $x$ from there. The two expressions are definitionally the same computation.
