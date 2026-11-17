<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Deciders.lean :: Complexity.Codec.cfgWord_le_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration Word Length Bound

**Claim.** For every Boolean list $r$, the encoded configuration word has length at most the length of the pair encoding of $x$ with the pair encoding of that configuration word and $r$.

**Proof.** The pair encoding of two lists has length twice the length of its first list, plus two separator bits, plus the length of its second list (`length_pairEncode`). Applying this formula twice, the outer encoding has length at least the length of its second component, which is itself a pair encoding containing the configuration word. That inner encoding has length at least the configuration word's length. Combining these inequalities proves the bound.

**Key facts.** `Turing.length_pairEncode`.
