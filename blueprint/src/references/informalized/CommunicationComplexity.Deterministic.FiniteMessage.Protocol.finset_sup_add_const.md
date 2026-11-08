<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/DetComposition.lean :: CommunicationComplexity.Deterministic.FiniteMessage.Protocol.finset_sup_add_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Supremum after adding a constant

**Claim.** For a finite nonempty index type, the supremum of the values $f(i)+c$ equals the supremum of $f(i)$ plus $c$.

**Proof.** For each index $i$, $f(i)$ is bounded above by the supremum of all values of $f$, so monotonicity of addition gives $f(i)+c\le (\sup_j f(j))+c$. Taking the supremum over $i$ proves one inequality. For the reverse inequality, finiteness and nonemptiness ensure that some index $j$ attains the supremum of $f$. Then $(\sup_i f(i))+c=f(j)+c$, which is one of the values whose supremum is being taken, proving the other inequality.
