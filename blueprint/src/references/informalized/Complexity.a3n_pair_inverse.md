<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a3n_pair_inverse -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inversion of Pair Decoding

**Claim.** For every finite Boolean word $z$ and all finite Boolean words $a,b$, if decoding $z$ yields $(a,b)$, then $z$ is the self-delimiting pair encoding of $a$ and $b$.

**Proof.** Induct on the structure of $z$, removing two leading bits at a time. The empty and one-bit cases cannot decode to a pair, since neither has the required delimiter. For a word beginning with $00$, successful decoding means the rest decodes to some $(u,v)$ and the decoded result is $(0u,v)$. By induction, that rest is the encoding of $(u,v)$; prefixing the duplicated $0$ gives the encoding of $(0u,v)$. The $11$ case is identical with a leading $1$. A prefix $01$ is the delimiter, so decoding returns $([],\text{rest})$, exactly the pair encoding with empty first component. A prefix $10$ cannot decode successfully. These cases establish the claim.
