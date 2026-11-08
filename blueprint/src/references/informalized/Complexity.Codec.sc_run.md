<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Run.lean :: Complexity.Codec.sc_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scan execution and register update

**Claim.** Under the stated register bound and total-capacity hypothesis, the simulator executes from scan state $c$ to its designated next state, zeroing the source register and adding the scan factor times its initial value to the destination while preserving the other registers and maintaining the guard and bound.

**Proof.** Use the register-scaling loop theorem with source and destination given by the scan registers, factor equal to the scan factor, and the scan state, decrement state, and increment labels as its test, decrement, and increment phases (`registerScale_loop`). The required source–destination distinctness is supplied by the fact that the scan source differs from its destination (`scSrc_ne`). The simulator definitions show that the test exits when the source is zero, each decrement is followed by the increment phase, and each of the factor-many increments raises the destination by one before returning to the test. The theorem’s capacity hypothesis is precisely the assumed bound on the destination’s initial value plus factor times the source’s initial value. It therefore yields the claimed endpoint valuation and guarded bounded execution.

**Key facts.** `Complexity.Codec.scSrc_ne`, `Complexity.LogProg.registerScale_loop`.
