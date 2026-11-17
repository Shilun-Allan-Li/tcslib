<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyCode.lean :: Randomized.PolyAmp.mem_initLang_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial-Configuration Language Characterization

**Claim.** The encoding of $x$, $c$, and $S$ belongs to the initial-configuration language of $N$ if and only if $c$ equals the code, at space bound $S$, of the initial configuration of $N$ on input $x$.

**Proof.** The membership characterization `mem_initLang` identifies membership of the encoded word with the equality $\operatorname{cfgCode}(S,\operatorname{initCfg}(x))=c$. Reversing the two sides of this equality gives exactly the claimed equivalence.

**Key facts.** `Complexity.Codec.mem_initLang`.
