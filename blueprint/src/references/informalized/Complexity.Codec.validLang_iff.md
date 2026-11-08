<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Checks.lean :: Complexity.Codec.validLang_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Valid configuration codes

**Claim.** The encoding of $x$ paired with the encoding of $w$ and the binary expansion of $s$ belongs to the valid-code language exactly when $w$ satisfies the four validity checks: the prescribed length, an accepting scan state, the bound on the encoded input-head position, and a final bit equal to $1$.

**Proof.** First use the characterization of valid checks (`validChk_iff`) to replace the four checks by the existence of a configuration $C$ on input $x$ that lies in the window of radius $s$ and whose configuration word is $w$. In the forward direction, membership supplies strings $x'$, $	ext{bits}(c)$, and $	ext{bits}(s')$ and a configuration on input $x'$. Injectivity of the pair encoding, applied twice, identifies $x'=x$ and the code string with $w$; injectivity of binary expansion then identifies $s'=s$. The remaining configuration and code equation give precisely the required witness, using the equivalence between equality of configuration code and equality of its word with the binary expansion (`cfgWord_eq_bits_iff`). Conversely, given such a configuration, choose its code for $c$ and choose $s$ as the encoded radius. The binary expansion of that code is its configuration word (`bits_cfgCode`), so the two nested pair encodings produce the required language witness.

**Key facts.** `Complexity.Codec.validChk_iff`, `Complexity.Codec.pairEncode_inj`, `Complexity.LogProg.bits_injective`, `Complexity.Codec.cfgWord_eq_bits_iff`, `Complexity.Codec.bits_cfgCode`.
