<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PreimageHost.lean :: Complexity.LogProg.OIS.ask_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Query Transition

**Claim.** From the encoded configuration in phase ask, one compiled-program step preserves the encoded machine configuration and auxiliary register, and sets the phase to bit exactly when the specified oracle query is answered true; otherwise it sets the phase to work with no pending write and a false left-boundary flag.

**Proof.** A run of length one is a single transition (`rrun_one`). At phase ask, the compiled program makes query number $0$ on the virtual input formed by pairing $x$ with the auxiliary register's binary word. The one-argument whole-input encoding is exactly this pair (`vword_whole₁`); the auxiliary tape contains the binary expansion of $i$ by the encoding, with `tapeWord_bufferTape` identifying its tape word. Thus the oracle answer selects phase bit when true and phase work with no pending write and false boundary flag when false. The query transition does not alter the represented machine configuration or the auxiliary register, giving the stated result.

**Key facts.** `Complexity.LogProg.rrun_one`, `Complexity.LogProg.vword_whole₁`, `Complexity.LogProg.tapeWord_bufferTape`.
