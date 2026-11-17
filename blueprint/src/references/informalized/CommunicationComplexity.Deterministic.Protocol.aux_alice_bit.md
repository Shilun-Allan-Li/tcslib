<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean :: CommunicationComplexity.Deterministic.Protocol.aux_alice_bit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Alice's Bit on a Leaf Rectangle

**Claim.** If $R$ is a leaf rectangle of $p$ formed with Alice's inputs restricted to $A\cap\{x:f(x)=b\}$ and Bob's inputs restricted to $B$, then every pair $(x,y)$ in $R$ satisfies $f(x)=b$.

**Proof.** The rectangle containment fact for the recursive leaf-rectangle construction says that every such $R$ is contained in the product of its two restricted input sets (\texttt{aux\_subset}). Thus, if $(x,y)\in R$, then $x\in A\cap\{x:f(x)=b\}$. Membership in this intersection gives $f(x)=b$, as required.

**Key facts.** `CommunicationComplexity.Deterministic.Protocol.aux_subset`.
