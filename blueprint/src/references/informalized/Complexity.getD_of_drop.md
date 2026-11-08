<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/VWord.lean :: Complexity.getD_of_drop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lookup after dropping a prefix

**Claim.** If dropping the first $p$ entries of $x$ gives the list beginning with $b$, then the entry of $x$ at index $p$, with false as the default, is $b$.

**Proof.** The lookup-after-dropping identity says that looking up index $i$ in the list obtained by dropping $a$ entries is the same as looking up index $a+i$ in the original list (`Complexity.getD_drop`). Apply it with $a=p$ and $i=0$. Since the dropped list is $b :: r$, its lookup at index $0$ is $b$. Thus $x$ looked up at index $p$ is $b$, as required.

**Key facts.** `Complexity.getD_drop`.
