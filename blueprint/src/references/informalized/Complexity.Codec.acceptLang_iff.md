<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Checks.lean :: Complexity.Codec.acceptLang_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Accepted language check characterization

**Claim.** Let $N$ be a nondeterministic Turing machine with Boolean input alphabet, and let $x,w$ be finite bit strings and $s$ a natural number. The paired encoding of $x$ with the paired encoding of $w$ and the binary expansion of $s$ belongs to the language of accepting configuration codes for $N$ if and only if $w$ passes the stated acceptance check.

**Proof.** First use the accepted-check characterization (\texttt{Complexity.Codec.acceptChk_iff}) to replace the check by the existence of an in-window configuration $C$ whose configuration word is the checked word, with halted state and output $[1]$.

If the paired encoding belongs to the language, its definition supplies an input string $x'$, numbers $c,s'$, and such a configuration, with the word encoded as the nested pair of $x'$, the bits of $c$, and the bits of $s'$. Injectivity of paired encoding (\texttt{Complexity.Codec.pairEncode_inj}), applied successively, identifies $x'=x$, the middle bit string with $w$, and the outer bit string with the bits of $s$. Injectivity of binary expansion (\texttt{Complexity.LogProg.bits_injective}) gives $s'=s$. The configuration’s code equality then says its configuration word is the bits of $c$; the code-word equivalence (\texttt{Complexity.Codec.cfgWord_eq_bits_iff}) turns this into the required equality with the checked word. The accepted-check characterization yields the check.

Conversely, take a configuration witnessing that characterization. Choose its code as the middle number and $s$ as the outer number. The fact that the bits of a configuration code are its configuration word (\texttt{Complexity.Codec.bits_cfgCode}) shows that the resulting paired encoding witnesses membership in the accepted language.

**Key facts.** `Complexity.Codec.acceptChk_iff`, `Complexity.Codec.pairEncode_inj`, `Complexity.LogProg.bits_injective`, `Complexity.Codec.cfgWord_eq_bits_iff`, `Complexity.Codec.bits_cfgCode`.
