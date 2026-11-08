<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost.lean :: Complexity.LogProg.OIS.bit_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Bit Query

**Claim.** For a configuration of the original machine in state $s$, one compiled-program step from the bit-query phase produces the same encoded configuration in the work phase, with pending bit $o(1,\langle x,\operatorname{bits}(i)\rangle)$ and left-boundary flag false.

**Proof.** A single iteration of the run is one program step (`rrun_one`). In the bit phase the program makes the query with index $1$, using the whole-input mode and the extra tape as its sole argument. That tape contains the binary expansion of $i$, so the decoded query word is $\langle x,\operatorname{bits}(i)\rangle$: the whole-input, single-argument encoding fact is `vword_whole₁`, and the buffer tape decodes to its stored word by `tapeWord_bufferTape`. The call therefore selects the positive or negative successor according as the oracle answer is true or false. These successors are exactly the work phase with that answer as the pending bit and flag false; splitting on the Boolean answer confirms the resulting configurations agree.

**Key facts.** `Complexity.LogProg.rrun_one`, `Complexity.LogProg.vword_whole₁`, `Complexity.LogProg.tapeWord_bufferTape`.
