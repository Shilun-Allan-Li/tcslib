<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Langs.lean :: Complexity.Codec.mem_initLang -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Configuration Language Membership

**Claim.** The nested paired encoding of $x$, the binary expansion of $c$, and the binary expansion of $s$ belongs to the initial-configuration language exactly when the code of $N$'s initial configuration on $x$, at window size $s$, equals $c$.

**Proof.** Unpack membership in the initial-configuration language. Its witnesses give an equality between the supplied nested paired encoding and the encoding of some $x',c',s'$, as well as the assertion that the initial configuration on $x'$ has code $c'$. Applying injectivity of paired encoding twice (`Complexity.Codec.pairEncode_inj`) identifies the inputs and the two encoded bit strings. Injectivity of binary expansion (`Complexity.LogProg.bits_injective`) then identifies $c'=c$ and $s'=s$, yielding the required code equality. Conversely, that equality witnesses membership by choosing $x,c,s$ in the language definition.

**Key facts.** `Complexity.Codec.pairEncode_inj`, `Complexity.LogProg.bits_injective`.
