<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Checks.lean :: Complexity.Codec.initLang_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Language Membership Characterization

**Claim.** The paired encoding of $x$, $w$, and the binary word for $s$ belongs to the initial language exactly when $w$ satisfies the initial-check conditions for $N$, $x$, and $s$.

**Proof.** Rewrite the initial-check condition using the characterization `initChk_iff`: it is equivalent to $w$ being the code of the initial configuration on $x$ with window parameter $s$. For the forward direction, membership supplies words and numbers $x',c,s'$ witnessing the language definition. Injectivity of the pairing encoding (`pairEncode_inj`), applied to the outer and then inner pair, identifies $x'=x$ and the encoded counter word with $w$. Injectivity of the binary-word encoding (`bits_injective`) then identifies $s'=s$. The remaining equality says that the code of the initial configuration equals $c$, which by `cfgWord_eq_bits_iff` is exactly the assertion that its configuration word is the binary word for $c$. Thus $w$ is that configuration word, as required by `initChk_iff`. Conversely, if $w$ is the initial configuration word, choose $c$ to be its numerical code and use $s$ itself as the window parameter. The equality `bits_cfgCode` says the binary word for this code is exactly the configuration word, giving the required language witness.

**Key facts.** `Complexity.Codec.initChk_iff`, `Complexity.Codec.pairEncode_inj`, `Complexity.LogProg.bits_injective`, `Complexity.Codec.cfgWord_eq_bits_iff`, `Complexity.Codec.bits_cfgCode`.
