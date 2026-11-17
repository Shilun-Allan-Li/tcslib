<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Checks.lean :: Complexity.Codec.stepLang_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Language Characterization by Step Checks

**Claim.** The self-delimiting pair encoding of $x,w,w'$ and the binary expansion of $s$ belongs to the bounded-space one-step transition language exactly when the step-check predicate holds.

**Proof.** Use `stepChk_iff` to replace the step-check predicate by the existence of two window-bounded configurations whose words are $w$ and $w'$ and which are related by one machine step. If the encoded string belongs to the language, its definition supplies lists $x'$, the two numeric configuration codes, and a space bound, together with such configurations. Repeated application of pair-encoding injectivity (`pairEncode_inj`) identifies each decoded component with the corresponding given component. Injectivity of the binary expansion (`bits_injective`) identifies the decoded bound with $s$. The equivalence `cfgWord_eq_bits_iff` then turns each equality between a configuration code and its number into the required equality of its configuration word with $w$ or $w'$.

Conversely, given the configurations supplied by `stepChk_iff`, choose their configuration codes as the two numbers in the language definition. By `bits_cfgCode`, the binary expansion of each chosen code is exactly its configuration word. The stipulated equalities of those words with $w$ and $w'$ therefore make the nested pair encoding equal to the requested string, yielding membership in the language.

**Key facts.** `Complexity.Codec.stepChk_iff`, `Complexity.Codec.pairEncode_inj`, `Complexity.LogProg.bits_injective`, `Complexity.Codec.cfgWord_eq_bits_iff`, `Complexity.Codec.bits_cfgCode`.
