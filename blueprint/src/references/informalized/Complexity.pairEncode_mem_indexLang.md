<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ImplicitPoly.lean :: Complexity.pairEncode_mem_indexLang -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership in an Indexed Language

**Claim.** The encoding of $x$ paired with the binary expansion of $i$ belongs to the language defined by a predicate $p$ exactly when $p(x,i)$ holds.

**Proof.** If the encoded word belongs to the language, its definition supplies strings $x'$ and a number $i'$ such that the word is the pair encoding of $x'$ and the binary expansion of $i'$, and $p(x',i')$ holds. Injectivity of pair encoding (`Turing.pairEncode_injective`) identifies both components: $x'=x$ and the binary expansions of $i'$ and $i$ agree. Injectivity of the binary-expansion map (`Complexity.LogProg.bits_injective`) then gives $i'=i$, so $p(x,i)$ follows. Conversely, if $p(x,i)$ holds, the language definition is witnessed directly by $x$ and $i$.

**Key facts.** `Turing.pairEncode_injective`, `Complexity.LogProg.bits_injective`.
