<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Langs.lean :: Complexity.Codec.mem_validLang -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Valid Configuration Language Membership

**Claim.** The nested paired encoding of $x$, the binary expansion of $c$, and the binary expansion of $s$ belongs to the valid-configuration language exactly when there is a configuration on input $x$ within window $s$ whose code is $c$.

**Proof.** Unpack membership in the valid-configuration language. Its witnesses give an equality between the given encoding and the encoding of some $x',c',s'$, together with a configuration on $x'$ in window $s'$ having code $c'$. Injectivity of paired encoding, applied to the outer pair and then the inner pair (`Complexity.Codec.pairEncode_inj`), identifies the inputs and the encoded binary strings. Injectivity of binary expansion (`Complexity.LogProg.bits_injective`) identifies $c'=c$ and $s'=s$. This yields the required configuration. Conversely, any configuration satisfying the claimed window and code conditions witnesses language membership by choosing $x,c,s$ directly.

**Key facts.** `Complexity.Codec.pairEncode_inj`, `Complexity.LogProg.bits_injective`.
