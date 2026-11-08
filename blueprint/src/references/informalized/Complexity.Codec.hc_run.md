<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Run.lean :: Complexity.Codec.hc_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halving and Bit-Length Accumulation

**Claim.** Starting from the halving-counter test state, the codec program reaches its copy phase for $E$, sets the halving counter to zero, and adds the binary expansion length of its former value to the work register. The safety condition holds throughout, and all register values remain at most $B$.

**Proof.** Apply the halving-count loop theorem (`halvCount_loop`) with the counter register as the loop variable and the work register as the accumulator. Its hypotheses match the program: at the test label, a zero counter proceeds to the destination, while a nonzero counter is halved and then the accumulator is incremented before testing again. The two registers are distinct, and the initial bounds and the assumed inequality $v(r_{m Wp})+|	ext{bits}(v(r_{m T}))|\le B$ are exactly the loop theorem's resource hypotheses. Thus the loop reaches the destination with the counter cleared and the accumulator increased by the counter's binary bit length, while the guard—and hence the stipulated safety and register bounds—holds at each prior configuration.

**Key facts.** `Complexity.Codec.halvCount_loop`.
