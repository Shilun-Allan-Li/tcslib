<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Langs.lean :: Complexity.Codec.mem_stepLang -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Language Membership

**Claim.** The paired encoding of $x,c,c',s$ belongs to the one-step language exactly when there are configurations $C,C'$ on input $x$ such that $C$ is within window $s$ and has code $c$, $C'$ follows from $C$ by one machine step and is also within the window, and $C'$ has code $c'$.

**Proof.** Unpack membership in the one-step language. The witnesses provide an equality of nested paired encodings and configurations with the stated window, code, and transition properties. Apply injectivity of paired encoding successively to the outer and inner pairs (`Complexity.Codec.pairEncode_inj`); then injectivity of binary expansion (`Complexity.LogProg.bits_injective`) identifies all three encoded natural numbers with $c,c',s$. The witnesses consequently satisfy the desired statement. Conversely, given such configurations, choose $x,c,c',s$ as the language witnesses; the encoding equality is reflexive.

**Key facts.** `Complexity.Codec.pairEncode_inj`, `Complexity.LogProg.bits_injective`.
