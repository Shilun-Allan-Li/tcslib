<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.vword_whole₁ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Whole Input with One Register

**Claim.** In whole-input mode, the virtual word built from input $u$ and the single register $r$ is the encoded pair $(u,V(r))$.

**Proof.** Whole-input mode makes the first segment $(u,\text{doubled})$, so its rendered word is the doubling of $u$. The single register segment contains $V(r)$ and is rendered plainly. The virtual-word definition places the separator $(0,1)$ between these two pieces. The identity `pairEncode_eq_dbl` says exactly that this concatenation is the encoding of $(u,V(r))$.

**Key facts.** `Turing.pairEncode_eq_dbl`.
