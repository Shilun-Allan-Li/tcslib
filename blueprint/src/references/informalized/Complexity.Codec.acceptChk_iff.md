<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Checks.lean :: Complexity.Codec.acceptChk_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of accepted configuration checks

**Claim.** A bit string $w$ satisfies the acceptance check for $x$ and window radius $s$ if and only if it is the encoded word of some configuration $C$ on input $x$ whose work-tape heads and nonblank cells lie within distance $s$ of the origin, with $C$ halted and its output exactly $[1]$.

**Proof.** For the forward implication, the valid-check characterization (\texttt{Complexity.Codec.validChk_iff}) supplies a configuration $C$ in the window whose encoded word is $w$. The acceptance check additionally says that the scan’s head-summary is $(\text{halted},1)$. By the configuration-word scan theorem (\texttt{Complexity.Codec.vScan_cfgWord}), this summary equals the encoding of $C$’s state and output summary. Equality of the first components gives that $C$ is halted. Equality of the second components, together with injectivity of the summary encoding (\texttt{Complexity.Codec.sumIdx_injective}), identifies $C$’s output summary as the accepting one. The characterization of that summary (\texttt{Turing.outSummary_eq_accept_iff}) says exactly that the output is $[1]$.

Conversely, suppose such a configuration $C$ exists and its encoded word is $w$. The reverse implication of the valid-check characterization gives the validity part of the acceptance check. Applying the configuration-word scan theorem to $C$, then using that its state is halted and its output is $[1]$, shows that the scanned head-summary is $(\text{halted},1)$. Hence the acceptance check holds.

**Key facts.** `Complexity.Codec.validChk_iff`, `Complexity.Codec.vScan_cfgWord`, `Complexity.Codec.sumIdx_injective`, `Turing.outSummary_eq_accept_iff`.
