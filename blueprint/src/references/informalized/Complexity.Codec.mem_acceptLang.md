<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Langs.lean :: Complexity.Codec.mem_acceptLang -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance Language Membership

**Claim.** The nested paired encoding of $x$, the binary expansion of $c$, and the binary expansion of $s$ belongs to the acceptance language exactly when there is a configuration on input $x$ within window $s$, with code $c$, halted state, and output $[1]$.

**Proof.** Unpack membership in the acceptance language. It supplies strings and numbers $x',c',s'$ whose nested paired encoding is the given one, together with a configuration satisfying the required window, code, halting, and output conditions. The injectivity of the pairing encoding (`Complexity.Codec.pairEncode_inj`), applied first to the outer pair and then to the inner pair, identifies $x'=x$ and the two encoded bit strings. Injectivity of the binary-expansion map (`Complexity.LogProg.bits_injective`) then gives $c'=c$ and $s'=s$, so the supplied configuration is the required witness. Conversely, any such configuration witnesses membership directly by choosing $x,c,s$ themselves in the language definition; the encodings then agree by reflexivity.

**Key facts.** `Complexity.Codec.pairEncode_inj`, `Complexity.LogProg.bits_injective`.
